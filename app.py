"""MarkerHome: cancer marker test booking (pincode + phone OTP registration + catalogue).

Single-file Streamlit app.   Run:  streamlit run app.py

Sections:  1 Config   2 Errors/validators/security   3 Database models   4 Seed data
           5 Services (SMS, auth, pincode, catalogue)   6 UI (theme, pages)   7 Entry point

Status: demo build. Booking (cart, slots, payment) is not included yet.
Prices, turnaround times and pincodes below are ILLUSTRATIVE: replace with your lab partner's data.
"""
from __future__ import annotations

import hashlib
import hmac
import html
import logging
import os
import re
import secrets
from contextlib import contextmanager
from dataclasses import dataclass, field
from datetime import date, datetime, timedelta, timezone
from functools import lru_cache
from pathlib import Path
from typing import Iterator, Literal

import streamlit as st
from sqlalchemy import (Boolean, Column, Date, DateTime, ForeignKey, Index, Integer, String, Table, Text,
                        UniqueConstraint, create_engine, event, func, or_, select)
from sqlalchemy.orm import (DeclarativeBase, Mapped, Session, mapped_column, relationship, selectinload,
                            sessionmaker)
from sqlalchemy.pool import StaticPool

log = logging.getLogger("markerhome")
BRAND = "MarkerHome"  # placeholder name: change freely
HERE = Path(__file__).resolve().parent


# ======================================================================================
# 1. CONFIG  (environment variables or Streamlit secrets)
# ======================================================================================

INSECURE_SECRET = "dev-insecure-secret-change-me"


def _env(name: str, default: str | None = None) -> str | None:
    value = os.environ.get(name)
    if value is not None:
        return value
    try:
        if name in st.secrets:
            return str(st.secrets[name])
    except Exception:  # no secrets file: normal in local development
        pass
    return default


@dataclass(frozen=True)
class Settings:
    app_env: str = "dev"                      # dev | production
    database_url: str = f"sqlite:///{HERE / 'marker_booking.db'}"
    secret_key: str = INSECURE_SECRET
    sms_provider: str = "console"             # console | msg91
    msg91_auth_key: str = ""
    msg91_template_id: str = ""
    otp_length: int = 6
    otp_ttl_seconds: int = 300
    otp_max_attempts: int = 5
    otp_resend_cooldown_seconds: int = 30
    otp_max_per_hour: int = 5
    show_dev_otp: bool = True                 # shows the OTP on screen. Must be False in production.
    session_ttl_days: int = 7
    consent_version: str = "2026-11-v1"

    def validate(self) -> None:
        if self.app_env != "production":
            return
        problems = []
        if self.secret_key == INSECURE_SECRET or len(self.secret_key) < 32:
            problems.append("SECRET_KEY must be a random value of at least 32 characters")
        if self.sms_provider == "console":
            problems.append("SMS_PROVIDER cannot be 'console'")
        if self.show_dev_otp:
            problems.append("SHOW_DEV_OTP must be false")
        if self.database_url.startswith("sqlite"):
            problems.append("use a hosted Postgres DATABASE_URL, not SQLite")
        if problems:
            raise ConfigError("Unsafe production configuration: " + "; ".join(problems))


@lru_cache(maxsize=1)
def get_settings() -> Settings:
    d = Settings()
    app_env = (_env("APP_ENV", "dev") or "dev").lower()
    provider = (_env("SMS_PROVIDER", "console") or "console").lower()
    show_default = app_env != "production" and provider == "console"
    flag = _env("SHOW_DEV_OTP")
    s = Settings(
        app_env=app_env,
        database_url=_env("DATABASE_URL", d.database_url),
        secret_key=_env("SECRET_KEY", d.secret_key),
        sms_provider=provider,
        msg91_auth_key=_env("MSG91_AUTH_KEY", "") or "",
        msg91_template_id=_env("MSG91_TEMPLATE_ID", "") or "",
        show_dev_otp=show_default if flag is None else flag.strip().lower() in {"1", "true", "yes", "on"},
    )
    s.validate()
    return s


# ======================================================================================
# 2. ERRORS, VALIDATORS, SECURITY
# ======================================================================================

class ServiceError(Exception):
    """Expected, user-presentable failure."""


class ValidationError(ServiceError):
    pass


class OtpError(ServiceError):
    pass


class RateLimited(ServiceError):
    def __init__(self, message: str, retry_after: int = 0):
        super().__init__(message)
        self.retry_after = retry_after


class ConfigError(Exception):
    pass


def utcnow() -> datetime:
    """Naive UTC everywhere (SQLite and Postgres behave the same). Tests monkeypatch this."""
    return datetime.now(timezone.utc).replace(tzinfo=None)


_PHONE_RE = re.compile(r"^[6-9]\d{9}$")
_PINCODE_RE = re.compile(r"^[1-9]\d{5}$")
_EMAIL_RE = re.compile(r"^[^@\s]+@[^@\s]+\.[^@\s]{2,}$")
SEX_OPTIONS = ("Male", "Female", "Other")
MIN_ACCOUNT_AGE = 18  # DPDP Act: valid consent for health data needs an adult


def normalize_phone(raw: str) -> str:
    """'98450 12345', '+91-98450-12345', '09845012345' -> '+919845012345'."""
    text = re.sub(r"[\s\-()]", "", (raw or "").strip())
    if text.startswith("+"):
        if not text.startswith("+91"):
            raise ValidationError("Only Indian mobile numbers (+91) are supported.")
        text = text[3:]
    elif text.startswith("0091"):
        text = text[4:]
    elif len(text) == 12 and text.startswith("91"):
        text = text[2:]
    elif len(text) == 11 and text.startswith("0"):
        text = text[1:]
    if not _PHONE_RE.match(text):
        raise ValidationError("Enter a valid 10-digit Indian mobile number.")
    return "+91" + text


def mask_phone(e164: str) -> str:
    d = e164[-10:]
    return f"+91 {d[:2]}{'X' * 6}{d[-2:]}"


def validate_pincode(raw: str) -> str:
    text = (raw or "").strip().replace(" ", "")
    if not _PINCODE_RE.match(text):
        raise ValidationError("Enter a valid 6-digit pincode.")
    return text


def validate_name(raw: str) -> str:
    name = re.sub(r"\s+", " ", (raw or "").strip())
    if len(name) < 2 or len(name) > 120:
        raise ValidationError("Enter your full name (2 to 120 characters).")
    if not re.match(r"^[^\d_@#$%^*=+<>{}\[\]\\|/~`]+$", name):
        raise ValidationError("Name can contain letters, spaces, dots, hyphens and apostrophes only.")
    return name


def validate_email(raw: str | None) -> str | None:
    text = (raw or "").strip().lower()
    if not text:
        return None
    if len(text) > 254 or not _EMAIL_RE.match(text):
        raise ValidationError("Enter a valid email address, or leave it blank.")
    return text


def validate_dob(value: date | None, *, min_age: int = 0, today: date | None = None) -> date:
    today = today or date.today()
    if value is None:
        raise ValidationError("Enter your date of birth.")
    if value > today:
        raise ValidationError("Date of birth cannot be in the future.")
    age = today.year - value.year - ((today.month, today.day) < (value.month, value.day))
    if age > 120:
        raise ValidationError("Enter a valid date of birth.")
    if age < min_age:
        raise ValidationError(f"You must be at least {min_age} years old to create an account.")
    return value


def validate_sex(raw: str) -> str:
    if raw not in SEX_OPTIONS:
        raise ValidationError("Select Male, Female or Other.")
    return raw


def generate_otp(length: int = 6) -> str:
    return "".join(secrets.choice("0123456789") for _ in range(length))


def hash_otp(phone: str, otp: str, key: str) -> str:
    """HMAC binds the OTP to the phone number and the server secret. The raw OTP is never stored."""
    return hmac.new(key.encode(), f"{phone}:{otp}".encode(), hashlib.sha256).hexdigest()


def hash_token(token: str) -> str:
    return hashlib.sha256(token.encode()).hexdigest()


def phone_fingerprint(phone: str, key: str) -> str:
    """Pseudonym for audit logs, so raw numbers never land in them."""
    return hmac.new(key.encode(), phone.encode(), hashlib.sha256).hexdigest()[:16]


# ======================================================================================
# 3. DATABASE (SQLAlchemy 2.0)
# ======================================================================================

class Base(DeclarativeBase):
    pass


_engine = None
_factory: sessionmaker[Session] | None = None


def init_engine(url: str | None = None):
    """(Re)initialise the global engine. Tests pass a URL; the app uses DATABASE_URL."""
    global _engine, _factory
    url = url or get_settings().database_url
    if url.startswith("sqlite"):
        kwargs: dict = {"connect_args": {"check_same_thread": False}}
        if ":memory:" in url or url == "sqlite://":
            kwargs["poolclass"] = StaticPool
        _engine = create_engine(url, **kwargs)

        @event.listens_for(_engine, "connect")
        def _fk_on(conn, _):
            conn.execute("PRAGMA foreign_keys=ON")
    else:
        _engine = create_engine(url, pool_pre_ping=True)
    _factory = sessionmaker(bind=_engine, expire_on_commit=False)
    return _engine


@contextmanager
def session_scope() -> Iterator[Session]:
    if _engine is None:
        init_engine()
    session = _factory()  # type: ignore[misc]
    try:
        yield session
        session.commit()
    except Exception:
        session.rollback()
        raise
    finally:
        session.close()


class User(Base):
    __tablename__ = "users"
    id: Mapped[int] = mapped_column(primary_key=True)
    phone: Mapped[str] = mapped_column(String(13), unique=True, index=True)  # +91XXXXXXXXXX
    name: Mapped[str | None] = mapped_column(String(120))
    email: Mapped[str | None] = mapped_column(String(254))
    dob: Mapped[date | None] = mapped_column(Date)
    sex: Mapped[str | None] = mapped_column(String(10))
    home_pincode: Mapped[str | None] = mapped_column(String(6))
    role: Mapped[str] = mapped_column(String(20), default="customer")
    is_active: Mapped[bool] = mapped_column(Boolean, default=True)
    created_at: Mapped[datetime] = mapped_column(DateTime, default=utcnow)
    last_login_at: Mapped[datetime | None] = mapped_column(DateTime)
    patients: Mapped[list["Patient"]] = relationship(back_populates="user", cascade="all, delete-orphan")

    @property
    def profile_complete(self) -> bool:
        return bool(self.name and self.dob and self.sex and self.home_pincode)


class Patient(Base):
    """Person a test is booked for. Every user gets a 'self' patient; family members come with booking."""
    __tablename__ = "patients"
    id: Mapped[int] = mapped_column(primary_key=True)
    user_id: Mapped[int] = mapped_column(ForeignKey("users.id", ondelete="CASCADE"), index=True)
    name: Mapped[str] = mapped_column(String(120))
    dob: Mapped[date] = mapped_column(Date)
    sex: Mapped[str] = mapped_column(String(10))
    relation: Mapped[str] = mapped_column(String(20), default="self")
    user: Mapped[User] = relationship(back_populates="patients")


class OtpRequest(Base):
    __tablename__ = "otp_requests"
    __table_args__ = (Index("ix_otp_phone_created", "phone", "created_at"),)
    id: Mapped[int] = mapped_column(primary_key=True)
    phone: Mapped[str] = mapped_column(String(13))
    otp_hash: Mapped[str] = mapped_column(String(64))
    expires_at: Mapped[datetime] = mapped_column(DateTime)
    attempts: Mapped[int] = mapped_column(Integer, default=0)
    used: Mapped[bool] = mapped_column(Boolean, default=False)
    created_at: Mapped[datetime] = mapped_column(DateTime, default=utcnow)


class UserSession(Base):
    __tablename__ = "user_sessions"
    id: Mapped[int] = mapped_column(primary_key=True)
    token_hash: Mapped[str] = mapped_column(String(64), unique=True, index=True)
    user_id: Mapped[int] = mapped_column(ForeignKey("users.id", ondelete="CASCADE"), index=True)
    created_at: Mapped[datetime] = mapped_column(DateTime, default=utcnow)
    expires_at: Mapped[datetime] = mapped_column(DateTime)
    revoked: Mapped[bool] = mapped_column(Boolean, default=False)


class ConsentRecord(Base):
    """DPDP Act: what the person agreed to, which wording version, and when."""
    __tablename__ = "consent_records"
    __table_args__ = (UniqueConstraint("user_id", "purpose", "version"),)
    id: Mapped[int] = mapped_column(primary_key=True)
    user_id: Mapped[int] = mapped_column(ForeignKey("users.id", ondelete="CASCADE"), index=True)
    purpose: Mapped[str] = mapped_column(String(40))  # terms_privacy | health_data | marketing
    version: Mapped[str] = mapped_column(String(20))
    granted: Mapped[bool] = mapped_column(Boolean, default=True)
    created_at: Mapped[datetime] = mapped_column(DateTime, default=utcnow)


class AuditLog(Base):
    __tablename__ = "audit_log"
    id: Mapped[int] = mapped_column(primary_key=True)
    actor_id: Mapped[int | None] = mapped_column(Integer)
    action: Mapped[str] = mapped_column(String(60), index=True)
    entity: Mapped[str | None] = mapped_column(String(40))
    entity_id: Mapped[str | None] = mapped_column(String(64))  # never a raw phone number
    created_at: Mapped[datetime] = mapped_column(DateTime, default=utcnow)


class ServiceablePincode(Base):
    __tablename__ = "serviceable_pincodes"
    pincode: Mapped[str] = mapped_column(String(6), primary_key=True)
    area: Mapped[str | None] = mapped_column(String(80))
    city: Mapped[str] = mapped_column(String(80))
    state: Mapped[str] = mapped_column(String(80))
    active: Mapped[bool] = mapped_column(Boolean, default=True)  # False = "coming soon"
    collection_fee: Mapped[int] = mapped_column(Integer, default=0)


class PincodeWaitlist(Base):
    __tablename__ = "pincode_waitlist"
    __table_args__ = (UniqueConstraint("pincode", "phone"),)
    id: Mapped[int] = mapped_column(primary_key=True)
    pincode: Mapped[str] = mapped_column(String(6), index=True)
    phone: Mapped[str | None] = mapped_column(String(13))
    created_at: Mapped[datetime] = mapped_column(DateTime, default=utcnow)


package_tests = Table(
    "package_tests", Base.metadata,
    Column("package_id", ForeignKey("packages.id", ondelete="CASCADE"), primary_key=True),
    Column("test_id", ForeignKey("tests.id", ondelete="CASCADE"), primary_key=True),
)


class Test(Base):
    __tablename__ = "tests"
    __test__ = False  # keep pytest from collecting this model
    id: Mapped[int] = mapped_column(primary_key=True)
    code: Mapped[str] = mapped_column(String(20), unique=True, index=True)
    name: Mapped[str] = mapped_column(String(120))
    category: Mapped[str] = mapped_column(String(40), index=True)
    description: Mapped[str] = mapped_column(Text, default="")
    sample_type: Mapped[str] = mapped_column(String(30), default="Serum")
    fasting_hours: Mapped[int] = mapped_column(Integer, default=0)
    tat_hours: Mapped[int] = mapped_column(Integer, default=24)
    price: Mapped[int] = mapped_column(Integer)  # whole rupees
    mrp: Mapped[int] = mapped_column(Integer)
    prep_notes: Mapped[str] = mapped_column(Text, default="")
    interference_notes: Mapped[str] = mapped_column(Text, default="")
    popular: Mapped[bool] = mapped_column(Boolean, default=False)
    active: Mapped[bool] = mapped_column(Boolean, default=True)


class Package(Base):
    __tablename__ = "packages"
    id: Mapped[int] = mapped_column(primary_key=True)
    code: Mapped[str] = mapped_column(String(30), unique=True, index=True)
    name: Mapped[str] = mapped_column(String(120))
    description: Mapped[str] = mapped_column(Text, default="")
    audience: Mapped[str] = mapped_column(String(10), default="all")  # all | male | female
    price: Mapped[int] = mapped_column(Integer)
    mrp: Mapped[int] = mapped_column(Integer)
    popular: Mapped[bool] = mapped_column(Boolean, default=False)
    active: Mapped[bool] = mapped_column(Boolean, default=True)
    tests: Mapped[list[Test]] = relationship(secondary=package_tests, order_by=Test.id)


# ======================================================================================
# 4. SEED DATA  (ILLUSTRATIVE prices / turnaround / pincodes: replace with your lab's data)
# ======================================================================================

def _t(code, name, category, popular, description, fasting, tat, price, mrp, prep, interference):
    return dict(code=code, name=name, category=category, popular=popular, description=description,
                sample_type="Serum", fasting_hours=fasting, tat_hours=tat, price=price, mrp=mrp,
                prep_notes=prep, interference_notes=interference)


SEED_TESTS = [
    _t("PSA-T", "PSA, Total", "Prostate", True,
       "Prostate-specific antigen. Used with a doctor's guidance for prostate evaluation and for monitoring known prostate disease.",
       0, 24, 450, 900,
       "Avoid ejaculation and vigorous cycling for about 48 hours before sampling. If you recently had a digital rectal exam, catheter or prostate procedure, tell the phlebotomist.",
       "Infection or inflammation of the prostate, recent procedures and some medicines (for example finasteride) can change PSA."),
    _t("PSA-F", "PSA, Free", "Prostate", False,
       "Free PSA and the free-to-total ratio, often ordered when total PSA is in the borderline range.",
       0, 24, 550, 1000,
       "Same preparation as Total PSA: avoid ejaculation and vigorous cycling for about 48 hours.",
       "Interpretation depends on the total PSA value. Discuss results with your doctor."),
    _t("CA125", "CA 125", "Ovary", True,
       "Cancer antigen 125. Mainly used to monitor ovarian cancer and response to treatment.",
       0, 24, 600, 1200,
       "No fasting needed. Mention if you are menstruating or pregnant.",
       "Can be raised by menstruation, endometriosis, fibroids, pregnancy and many non-cancer conditions."),
    _t("HE4", "HE4", "Ovary", False,
       "Human epididymis protein 4. Sometimes used alongside CA 125 for ovarian evaluation.",
       0, 48, 1800, 3600, "No fasting needed.", "Kidney disease and smoking can raise HE4."),
    _t("CEA", "CEA (Carcinoembryonic Antigen)", "Colon and Rectum", True,
       "Mostly used to monitor colorectal cancer after treatment. Also raised in several other cancers.",
       0, 24, 500, 1000,
       "No fasting needed. Tell the phlebotomist if you smoke.",
       "Smokers have higher baseline levels. Inflammatory bowel disease, liver disease and infections can raise CEA."),
    _t("AFP", "AFP (Alpha-Fetoprotein)", "Liver", True,
       "Used to monitor liver cancer and certain germ cell tumours, and in surveillance of people with chronic liver disease.",
       0, 24, 450, 900, "No fasting needed. Mention if you are pregnant.",
       "Raised in pregnancy, hepatitis and cirrhosis."),
    _t("CA199", "CA 19-9", "Pancreas and Bile Duct", True,
       "Mainly used to monitor pancreatic and bile duct cancers during and after treatment.",
       0, 24, 650, 1300, "No fasting needed.",
       "Bile duct blockage, pancreatitis and liver disease can raise it. Not reliable in people who are Lewis-antigen negative."),
    _t("CA153", "CA 15-3", "Breast", True,
       "Used to monitor breast cancer treatment and recurrence. It is not a screening test for breast cancer.",
       0, 24, 650, 1300, "No fasting needed.",
       "Can be raised by benign breast disease, liver disease and other conditions."),
    _t("BHCG", "Beta-hCG (Total)", "Germ Cell and Trophoblastic", False,
       "Used to monitor certain testicular, ovarian germ cell and trophoblastic tumours. Also raised in pregnancy.",
       0, 24, 550, 1100, "No fasting needed. Tell us if you could be pregnant.",
       "Pregnancy is the commonest cause of a raised value."),
    _t("CALCI", "Calcitonin", "Thyroid", False,
       "Used in the evaluation and follow-up of medullary thyroid cancer.",
       8, 48, 1100, 2200,
       "Overnight fasting of 8 hours is commonly advised. Water is fine. Tell the phlebotomist about acid-reducing medicines.",
       "Acid-reducing medicines, kidney disease and some other conditions can raise calcitonin."),
    _t("TG", "Thyroglobulin", "Thyroid", False,
       "Used to follow people treated for differentiated thyroid cancer.",
       0, 48, 900, 1800, "No fasting needed. Bring your previous reports if you have them.",
       "Thyroglobulin antibodies can give falsely low results, so labs usually test antibodies as well."),
    _t("NSE", "NSE (Neuron-Specific Enolase)", "Lung and Neuroendocrine", False,
       "Used to monitor small cell lung cancer and neuroendocrine tumours.",
       0, 48, 1200, 2400, "No fasting needed. The sample must be handled carefully and processed quickly.",
       "Haemolysed (damaged) blood samples give falsely high values."),
    _t("CYFRA", "CYFRA 21-1", "Lung and Neuroendocrine", False,
       "Used to monitor non-small cell lung cancer, especially squamous cell type.",
       0, 48, 1100, 2200, "No fasting needed.",
       "Kidney failure and some lung and liver conditions can raise it."),
]

SEED_PACKAGES = [
    dict(code="PKG-MALE", name="Male Cancer Marker Panel", audience="male", popular=True, price=1599, mrp=3100,
         description="Prostate, liver and gastrointestinal markers in one visit. Best ordered on a doctor's advice.",
         tests=["PSA-T", "CEA", "AFP", "CA199"]),
    dict(code="PKG-FEMALE", name="Female Cancer Marker Panel", audience="female", popular=True, price=1799, mrp=3600,
         description="Ovarian, breast, liver and gastrointestinal markers in one visit. Best ordered on a doctor's advice.",
         tests=["CA125", "CA153", "CEA", "AFP"]),
    dict(code="PKG-EXTENDED", name="Extended Marker Panel (All Adults)", audience="all", popular=False,
         price=3299, mrp=6600,
         description="Broad panel covering the gastrointestinal, liver, pancreas and lung markers.",
         tests=["CEA", "AFP", "CA199", "CYFRA", "NSE"]),
    dict(code="PKG-THYROID-FU", name="Thyroid Cancer Follow-up Panel", audience="all", popular=False,
         price=1699, mrp=4000,
         description="For people already treated for thyroid cancer. Thyroglobulin and calcitonin.",
         tests=["TG", "CALCI"]),
]

# (pincode, area, city, state, active, collection_fee). active=False means "coming soon".
SEED_PINCODES = [
    ("560001", None, "Bengaluru", "Karnataka", True, 0), ("560002", None, "Bengaluru", "Karnataka", True, 0),
    ("560003", "Malleswaram", "Bengaluru", "Karnataka", True, 0),
    ("560004", "Basavanagudi", "Bengaluru", "Karnataka", True, 0),
    ("560008", "Ulsoor", "Bengaluru", "Karnataka", True, 0),
    ("560010", "Rajajinagar", "Bengaluru", "Karnataka", True, 0),
    ("560011", "Jayanagar", "Bengaluru", "Karnataka", True, 0),
    ("560025", None, "Bengaluru", "Karnataka", True, 0),
    ("560034", "Koramangala", "Bengaluru", "Karnataka", True, 0),
    ("560037", "Marathahalli", "Bengaluru", "Karnataka", True, 0),
    ("560038", "Indiranagar", "Bengaluru", "Karnataka", True, 0),
    ("560066", "Whitefield", "Bengaluru", "Karnataka", True, 0),
    ("560076", None, "Bengaluru", "Karnataka", True, 0),
    ("560078", "JP Nagar", "Bengaluru", "Karnataka", True, 0),
    ("560100", "Electronic City", "Bengaluru", "Karnataka", True, 0),
    ("560102", "HSR Layout", "Bengaluru", "Karnataka", True, 0),
    ("400001", None, "Mumbai", "Maharashtra", True, 50), ("110001", None, "New Delhi", "Delhi", True, 50),
    ("600001", None, "Chennai", "Tamil Nadu", True, 50), ("500001", None, "Hyderabad", "Telangana", True, 50),
    ("411001", None, "Pune", "Maharashtra", True, 50),
    ("700001", None, "Kolkata", "West Bengal", False, 0), ("380001", None, "Ahmedabad", "Gujarat", False, 0),
]


def seed_all(db: Session) -> None:
    """Idempotent: safe on every start. Updates existing rows by code / pincode."""
    by_code: dict[str, Test] = {}
    for item in SEED_TESTS:
        t = db.scalar(select(Test).where(Test.code == item["code"])) or Test(code=item["code"], name="",
                                                                              category="", price=0, mrp=0)
        for k, v in item.items():
            setattr(t, k, v)
        db.add(t)
        by_code[item["code"]] = t
    db.flush()
    for item in SEED_PACKAGES:
        p = db.scalar(select(Package).where(Package.code == item["code"])) or Package(code=item["code"], name="",
                                                                                      price=0, mrp=0)
        for k, v in item.items():
            if k != "tests":
                setattr(p, k, v)
        p.tests = [by_code[c] for c in item["tests"]]
        db.add(p)
    for pin, area, city, state, active, fee in SEED_PINCODES:
        row = db.get(ServiceablePincode, pin) or ServiceablePincode(pincode=pin, city="", state="")
        row.area, row.city, row.state, row.active, row.collection_fee = area, city, state, active, fee
        db.add(row)
    db.commit()


# ======================================================================================
# 5. SERVICES  (return plain dataclasses, never ORM objects, so Streamlit reruns stay safe)
# ======================================================================================

# ---- SMS ---------------------------------------------------------------------------

class SmsDeliveryError(Exception):
    pass


class ConsoleSms:
    """Development only: sends nothing. The UI shows the OTP when SHOW_DEV_OTP is on."""
    name = "console"

    def send_otp(self, phone: str, otp: str, ttl_minutes: int) -> None:
        log.warning("DEV OTP for %s: %s (valid %d min)", mask_phone(phone), otp, ttl_minutes)


class Msg91Sms:
    """MSG91 OTP API v5. UNVERIFIED against a live account: check current MSG91 docs and your
    DLT-approved template before go-live (India requires DLT registration for transactional SMS)."""
    name = "msg91"
    URL = "https://control.msg91.com/api/v5/otp"

    def __init__(self, auth_key: str, template_id: str):
        if not auth_key or not template_id:
            raise SmsDeliveryError("MSG91_AUTH_KEY and MSG91_TEMPLATE_ID are required")
        self.auth_key, self.template_id = auth_key, template_id

    def send_otp(self, phone: str, otp: str, ttl_minutes: int) -> None:
        import requests  # imported lazily: only needed for real SMS
        try:
            resp = requests.post(
                self.URL, timeout=10,
                params={"template_id": self.template_id, "mobile": phone.lstrip("+"), "otp": otp,
                        "otp_expiry": ttl_minutes},
                headers={"authkey": self.auth_key, "Content-Type": "application/json"})
            resp.raise_for_status()
        except requests.RequestException as exc:
            raise SmsDeliveryError("SMS provider request failed") from exc


def get_sms_provider(s: Settings):
    return Msg91Sms(s.msg91_auth_key, s.msg91_template_id) if s.sms_provider == "msg91" else ConsoleSms()


# ---- Auth --------------------------------------------------------------------------

@dataclass(frozen=True)
class OtpIssued:
    phone: str
    expires_at: datetime
    dev_otp: str | None  # only set when SHOW_DEV_OTP is on


@dataclass(frozen=True)
class CurrentUser:
    user_id: int
    phone: str
    name: str | None
    email: str | None
    dob: date | None
    sex: str | None
    home_pincode: str | None
    role: str
    profile_complete: bool


@dataclass(frozen=True)
class LoginResult:
    token: str
    user: CurrentUser
    is_new_user: bool


def _dto(u: User) -> CurrentUser:
    return CurrentUser(u.id, u.phone, u.name, u.email, u.dob, u.sex, u.home_pincode, u.role, u.profile_complete)


def audit(db: Session, action: str, *, actor_id: int | None = None, entity: str | None = None,
          entity_id: str | int | None = None) -> None:
    db.add(AuditLog(actor_id=actor_id, action=action, entity=entity,
                    entity_id=None if entity_id is None else str(entity_id)))


def request_otp(db: Session, phone_raw: str, *, settings: Settings | None = None, sms=None) -> OtpIssued:
    s = settings or get_settings()
    phone = normalize_phone(phone_raw)
    now = utcnow()

    last = db.scalar(select(OtpRequest).where(OtpRequest.phone == phone).order_by(OtpRequest.created_at.desc()).limit(1))
    if last is not None:
        wait = int(s.otp_resend_cooldown_seconds - (now - last.created_at).total_seconds())
        if wait > 0:
            raise RateLimited(f"Please wait {wait} seconds before requesting another code.", wait)
    sent = db.scalar(select(func.count()).select_from(OtpRequest).where(
        OtpRequest.phone == phone, OtpRequest.created_at >= now - timedelta(hours=1))) or 0
    if sent >= s.otp_max_per_hour:
        raise RateLimited("Too many codes requested. Try again in an hour.", 3600)

    for old in db.scalars(select(OtpRequest).where(OtpRequest.phone == phone, OtpRequest.used.is_(False))):
        old.used = True  # only the newest code is valid

    otp = generate_otp(s.otp_length)
    db.add(OtpRequest(phone=phone, otp_hash=hash_otp(phone, otp, s.secret_key), created_at=now,
                      expires_at=now + timedelta(seconds=s.otp_ttl_seconds)))
    db.flush()
    try:
        (sms or get_sms_provider(s)).send_otp(phone, otp, s.otp_ttl_seconds // 60)
    except SmsDeliveryError as exc:
        db.rollback()
        raise ServiceError("We couldn't send the SMS right now. Please try again shortly.") from exc
    audit(db, "otp_requested", entity="phone", entity_id=phone_fingerprint(phone, s.secret_key))
    db.commit()
    return OtpIssued(phone, now + timedelta(seconds=s.otp_ttl_seconds), otp if s.show_dev_otp else None)


def verify_otp(db: Session, phone_raw: str, otp_raw: str, *, settings: Settings | None = None) -> LoginResult:
    s = settings or get_settings()
    phone = normalize_phone(phone_raw)
    otp = (otp_raw or "").strip()
    if not re.fullmatch(rf"\d{{{s.otp_length}}}", otp):
        raise OtpError(f"Enter the {s.otp_length}-digit code.")
    now = utcnow()
    req = db.scalar(select(OtpRequest).where(OtpRequest.phone == phone, OtpRequest.used.is_(False))
                    .order_by(OtpRequest.created_at.desc()).limit(1))
    if req is None or req.expires_at <= now:
        raise OtpError("This code has expired or was never requested. Request a new code.")

    req.attempts += 1
    if not hmac.compare_digest(hash_otp(phone, otp, s.secret_key), req.otp_hash):
        left = s.otp_max_attempts - req.attempts
        if left <= 0:
            req.used = True
        db.commit()  # persist the failed attempt
        if left <= 0:
            raise OtpError("Too many incorrect attempts. Request a new code.")
        raise OtpError(f"Incorrect code. {left} attempt{'s' if left != 1 else ''} left.")

    req.used = True
    user = db.scalar(select(User).where(User.phone == phone))
    is_new = user is None
    if user is None:
        user = User(phone=phone)
        db.add(user)
        db.flush()
    if not user.is_active:
        db.commit()
        raise ServiceError("This account has been disabled. Contact support.")
    user.last_login_at = now
    token = secrets.token_urlsafe(32)
    db.add(UserSession(token_hash=hash_token(token), user_id=user.id, created_at=now,
                       expires_at=now + timedelta(days=s.session_ttl_days)))
    audit(db, "login", actor_id=user.id, entity="user", entity_id=user.id)
    db.commit()
    return LoginResult(token, _dto(user), is_new)


def get_current_user(db: Session, token: str | None) -> CurrentUser | None:
    if not token:
        return None
    sess = db.scalar(select(UserSession).where(UserSession.token_hash == hash_token(token)))
    if sess is None or sess.revoked or sess.expires_at <= utcnow():
        return None
    user = db.get(User, sess.user_id)
    return _dto(user) if user is not None and user.is_active else None


def logout(db: Session, token: str | None) -> None:
    if not token:
        return
    sess = db.scalar(select(UserSession).where(UserSession.token_hash == hash_token(token)))
    if sess is not None and not sess.revoked:
        sess.revoked = True
        audit(db, "logout", actor_id=sess.user_id, entity="user", entity_id=sess.user_id)
        db.commit()


def _apply_profile(user: User, *, name, email, dob, sex, pincode) -> None:
    user.name = validate_name(name)
    user.email = validate_email(email)
    user.dob = validate_dob(dob, min_age=MIN_ACCOUNT_AGE)
    user.sex = validate_sex(sex)
    user.home_pincode = validate_pincode(pincode)
    me = next((p for p in user.patients if p.relation == "self"), None)
    if me is None:
        user.patients.append(Patient(name=user.name, dob=user.dob, sex=user.sex, relation="self"))
    else:
        me.name, me.dob, me.sex = user.name, user.dob, user.sex


def complete_profile(db: Session, user_id: int, *, name, email, dob, sex, pincode, accept_terms: bool,
                     accept_health_data: bool, marketing: bool = False,
                     settings: Settings | None = None) -> CurrentUser:
    """First-time registration. Terms and health-data consent are separate and both mandatory."""
    s = settings or get_settings()
    if not accept_terms:
        raise ValidationError("Accept the Terms of Service and Privacy Policy to continue.")
    if not accept_health_data:
        raise ValidationError("We need your consent to process health data to book tests for you.")
    user = db.get(User, user_id)
    if user is None:
        raise ServiceError("Account not found.")
    _apply_profile(user, name=name, email=email, dob=dob, sex=sex, pincode=pincode)
    for purpose, granted in (("terms_privacy", True), ("health_data", True), ("marketing", marketing)):
        row = db.scalar(select(ConsentRecord).where(ConsentRecord.user_id == user_id, ConsentRecord.purpose == purpose,
                                                    ConsentRecord.version == s.consent_version))
        if row is None:
            db.add(ConsentRecord(user_id=user_id, purpose=purpose, version=s.consent_version, granted=granted))
        else:
            row.granted = granted
    audit(db, "profile_completed", actor_id=user_id, entity="user", entity_id=user_id)
    db.commit()
    return _dto(user)


def update_profile(db: Session, user_id: int, *, name, email, dob, sex, pincode) -> CurrentUser:
    user = db.get(User, user_id)
    if user is None:
        raise ServiceError("Account not found.")
    _apply_profile(user, name=name, email=email, dob=dob, sex=sex, pincode=pincode)
    audit(db, "profile_updated", actor_id=user_id, entity="user", entity_id=user_id)
    db.commit()
    return _dto(user)


# ---- Pincode -----------------------------------------------------------------------

@dataclass(frozen=True)
class Serviceability:
    pincode: str
    status: Literal["serviceable", "coming_soon", "unknown"]
    city: str | None = None
    state: str | None = None
    area: str | None = None
    collection_fee: int = 0

    @property
    def serviceable(self) -> bool:
        return self.status == "serviceable"

    @property
    def place(self) -> str:
        return ", ".join(p for p in (self.area, self.city) if p) or (self.state or "")


def check_pincode(db: Session, raw: str) -> Serviceability:
    pin = validate_pincode(raw)
    row = db.get(ServiceablePincode, pin)
    if row is None:
        return Serviceability(pin, "unknown")
    return Serviceability(pin, "serviceable" if row.active else "coming_soon", row.city, row.state, row.area,
                          row.collection_fee)


def join_waitlist(db: Session, raw_pincode: str, raw_phone: str | None = None) -> bool:
    """True if newly added, False if already on the list."""
    pin = validate_pincode(raw_pincode)
    phone = normalize_phone(raw_phone) if raw_phone else None
    if db.scalar(select(PincodeWaitlist).where(PincodeWaitlist.pincode == pin, PincodeWaitlist.phone == phone)):
        return False
    db.add(PincodeWaitlist(pincode=pin, phone=phone))
    db.commit()
    return True


# ---- Catalogue ---------------------------------------------------------------------

@dataclass(frozen=True)
class TestDTO:
    __test__ = False
    code: str
    name: str
    category: str
    description: str
    sample_type: str
    fasting_hours: int
    tat_hours: int
    price: int
    mrp: int
    prep_notes: str
    interference_notes: str
    popular: bool

    @property
    def discount_pct(self) -> int:
        return round(100 * (self.mrp - self.price) / self.mrp) if self.mrp > self.price else 0


@dataclass(frozen=True)
class PackageDTO:
    code: str
    name: str
    description: str
    audience: str
    price: int
    mrp: int
    popular: bool
    tests: list[TestDTO] = field(default_factory=list)

    @property
    def discount_pct(self) -> int:
        return round(100 * (self.mrp - self.price) / self.mrp) if self.mrp > self.price else 0

    @property
    def fasting_hours(self) -> int:
        return max((t.fasting_hours for t in self.tests), default=0)

    @property
    def tat_hours(self) -> int:
        return max((t.tat_hours for t in self.tests), default=0)


def _test_dto(t: Test) -> TestDTO:
    return TestDTO(t.code, t.name, t.category, t.description, t.sample_type, t.fasting_hours, t.tat_hours,
                   t.price, t.mrp, t.prep_notes, t.interference_notes, t.popular)


def list_categories(db: Session) -> list[str]:
    return list(db.scalars(select(Test.category).where(Test.active.is_(True)).distinct().order_by(Test.category)))


def search_tests(db: Session, query: str = "", category: str | None = None, no_fasting_only: bool = False) -> list[TestDTO]:
    stmt = select(Test).where(Test.active.is_(True))
    q = (query or "").strip()
    if q:
        like = f"%{q}%"
        stmt = stmt.where(or_(Test.name.ilike(like), Test.code.ilike(like), Test.category.ilike(like),
                              Test.description.ilike(like)))
    if category:
        stmt = stmt.where(Test.category == category)
    if no_fasting_only:
        stmt = stmt.where(Test.fasting_hours == 0)
    return [_test_dto(t) for t in db.scalars(stmt.order_by(Test.popular.desc(), Test.name))]


def list_packages(db: Session, audience: str | None = None) -> list[PackageDTO]:
    stmt = select(Package).options(selectinload(Package.tests)).where(Package.active.is_(True))
    if audience in {"male", "female"}:
        stmt = stmt.where(Package.audience.in_(["all", audience]))
    return [PackageDTO(p.code, p.name, p.description, p.audience, p.price, p.mrp, p.popular,
                       [_test_dto(t) for t in p.tests])
            for p in db.scalars(stmt.order_by(Package.popular.desc(), Package.name))]


# ======================================================================================
# 6. UI
# ======================================================================================

INK, STEEL, SERUM, RULE = "#12283A", "#1F5F8B", "#D9A21B", "#CBD9E1"

CSS = f"""
<style>
@import url('https://fonts.googleapis.com/css2?family=Bricolage+Grotesque:opsz,wght@12..96,500;12..96,700&family=Figtree:wght@400;500;600&display=swap');
html, body, .stApp, [class*="css"] {{ font-family: 'Figtree', system-ui, -apple-system, 'Segoe UI', sans-serif; }}
h1, h2, h3 {{ font-family: 'Bricolage Grotesque', 'Figtree', system-ui, sans-serif; color: {INK}; letter-spacing: -0.015em; }}
.block-container {{ max-width: 980px; padding-top: 2.2rem; padding-bottom: 4rem; }}
.cm-brand {{ font-family: 'Bricolage Grotesque', sans-serif; font-weight: 700; font-size: 1.35rem; color: {INK}; margin: 0; }}
.cm-brand span {{ color: {STEEL}; }}
.cm-hero h1 {{ font-size: clamp(2rem, 5vw, 3.1rem); line-height: 1.08; margin: .6rem 0 .5rem; max-width: 18ch; }}
.cm-hero p {{ font-size: 1.08rem; max-width: 52ch; color: #35505F; margin: 0 0 1.2rem; }}
.cm-status {{ border-left: 5px solid {STEEL}; background: #fff; padding: .85rem 1.1rem; border-radius: 4px; margin: .75rem 0 1rem; }}
.cm-status b {{ display: block; font-size: 1.05rem; margin-bottom: .15rem; }}
.cm-status.ok {{ border-left-color: #1E7F5C; }} .cm-status.soon {{ border-left-color: {SERUM}; }} .cm-status.no {{ border-left-color: #B3261E; }}
.cm-chips {{ display: flex; flex-wrap: wrap; gap: .35rem; margin: .3rem 0 .6rem; }}
.cm-chip {{ font-size: .8rem; padding: .12rem .55rem; border-radius: 999px; background: #E4EDF1; color: {INK}; border: 1px solid {RULE}; }}
.cm-chip.gold {{ background: #FBF0D0; border-color: #EBD28A; }} .cm-chip.green {{ background: #DDF1E8; border-color: #A9D8C2; }}
.cm-title {{ font-family: 'Bricolage Grotesque', sans-serif; font-weight: 700; font-size: 1.2rem; color: {INK}; margin: 0; }}
.cm-muted {{ color: #52687A; font-size: .93rem; }}
.cm-price {{ font-size: 1.35rem; font-weight: 600; color: {INK}; }}
.cm-price s {{ font-size: .95rem; font-weight: 400; color: #6B8091; margin-left: .4rem; }}
.cm-price em {{ font-style: normal; font-size: .85rem; color: #1E7F5C; margin-left: .4rem; font-weight: 600; }}
.cm-advisory {{ background: #FFF6DD; border: 1px solid #EBD28A; border-radius: 6px; padding: .7rem .95rem; font-size: .92rem; color: #4A3A0A; }}
.cm-footer {{ margin-top: 3rem; padding-top: 1rem; border-top: 1px solid {RULE}; font-size: .85rem; color: #52687A; }}
div[data-testid="stForm"] {{ background: #fff; border: 1px solid {RULE}; border-radius: 8px; }}
div[data-testid="stVerticalBlockBorderWrapper"] {{ border-color: {RULE}; background: #fff; }}
button:focus-visible, input:focus-visible {{ outline: 3px solid {SERUM} !important; outline-offset: 2px; }}
@media (prefers-reduced-motion: reduce) {{ * {{ transition: none !important; animation: none !important; }} }}
</style>
"""

ADVISORY = ("Tumour markers are not stand-alone screening tests for cancer. Normal values do not rule cancer out "
            "and raised values do not confirm it. They are used with examination, imaging and a doctor's advice, "
            "and most often to monitor known disease. Please discuss your results with your doctor.")


def esc(text: object) -> str:
    return html.escape(str(text), quote=True)


def chips(items: list[tuple[str, str]]) -> None:
    body = "".join(f'<span class="cm-chip {k}">{esc(t)}</span>' for t, k in items)
    st.markdown(f'<div class="cm-chips">{body}</div>', unsafe_allow_html=True)


def status_box(kind: str, title: str, body: str) -> None:
    st.markdown(f'<div class="cm-status {kind}"><b>{esc(title)}</b>{esc(body)}</div>', unsafe_allow_html=True)


def price_html(price: int, mrp: int, discount: int) -> str:
    strike = f"<s>₹{mrp:,}</s>" if mrp > price else ""
    off = f"<em>{discount}% off</em>" if discount else ""
    return f'<div class="cm-price">₹{price:,}{strike}{off}</div>'


def advisory() -> None:
    st.markdown(f'<div class="cm-advisory"><b>Before you book.</b> {esc(ADVISORY)}</div>', unsafe_allow_html=True)


# ---- session helpers ---------------------------------------------------------------
# Limitation: the token lives in st.session_state, so a browser refresh signs the person out.

PAGES: dict[str, object] = {}  # filled by main() so pages can link to each other


def current_user() -> CurrentUser | None:
    """Re-validated against the DB on every rerun, so expired or revoked sessions drop at once."""
    token = st.session_state.get("session_token")
    if not token:
        return None
    with session_scope() as db:
        user = get_current_user(db, token)
    if user is None:
        st.session_state.pop("session_token", None)
    return user


def is_authenticated(user: CurrentUser | None) -> bool:
    return bool(user and user.profile_complete)


def clear_auth_flow() -> None:
    for key in ("auth_step", "auth_phone", "auth_dev_otp"):
        st.session_state.pop(key, None)


def get_pincode_info() -> Serviceability | None:
    return st.session_state.get("pincode_info")


def set_pincode_info(info: Serviceability, source_key: str | None = None) -> None:
    """Pass the text_input key the value came from so that box isn't re-seeded over fresh typing."""
    st.session_state["pincode_info"] = info
    if source_key:
        st.session_state[f"_{source_key}_seeded"] = info.pincode


def sync_pincode_input(key: str) -> None:
    """Call BEFORE creating a pincode text_input. Gives it a stable key and re-seeds it when the stored
    pincode changed somewhere else (e.g. the header popover)."""
    info = get_pincode_info()
    current = info.pincode if info else ""
    marker = f"_{key}_seeded"
    if key not in st.session_state or st.session_state.get(marker) != current:
        st.session_state[key] = current
        st.session_state[marker] = current


def pincode_result(info: Serviceability, *, key: str) -> None:
    if info.serviceable:
        fee = ("Home collection is free." if info.collection_fee == 0
               else f"Home collection fee: ₹{info.collection_fee}.")
        status_box("ok", f"We collect samples at {info.pincode} ({info.place})", fee)
        return
    if info.status == "coming_soon":
        status_box("soon", f"{info.pincode} ({info.place}) is coming soon",
                   "We are not collecting there yet. Leave your number and we'll tell you the day we start.")
    else:
        status_box("no", f"We don't cover {info.pincode} yet",
                   "Leave your number and we'll tell you if that changes.")
    with st.form(f"waitlist_{key}", clear_on_submit=True):
        phone = st.text_input("Mobile number (optional)", max_chars=16, key=f"wl_phone_{key}")
        if st.form_submit_button("Notify me"):
            try:
                with session_scope() as db:
                    added = join_waitlist(db, info.pincode, phone or None)
                st.success("You're on the list." if added else "You're already on the list for this pincode.")
            except ServiceError as exc:
                st.error(str(exc))


# ---- pages -------------------------------------------------------------------------

def page_home() -> None:
    st.markdown('<div class="cm-hero"><h1>Cancer marker blood tests, collected at home.</h1>'
                "<p>Enter your pincode to see whether a phlebotomist can reach you. "
                "Reports are delivered online from an accredited laboratory.</p></div>", unsafe_allow_html=True)
    info = get_pincode_info()
    sync_pincode_input("home_pincode")
    with st.form("home_pincode_form"):
        pincode = st.text_input("Your pincode", key="home_pincode", max_chars=6, placeholder="e.g. 560034")
        submitted = st.form_submit_button("Check availability", type="primary")
    if submitted:
        try:
            with session_scope() as db:
                info = check_pincode(db, pincode)
            set_pincode_info(info, "home_pincode")
        except ServiceError as exc:
            st.error(str(exc))
            info = None
    if info:
        pincode_result(info, key="home")
        if info.serviceable and not is_authenticated(current_user()) and "login" in PAGES:
            st.page_link(PAGES["login"], label="Create an account or sign in")

    advisory()
    with session_scope() as db:
        popular = [p for p in list_packages(db) if p.popular]
    if popular:
        st.subheader("Popular panels")
        for col, pkg in zip(st.columns(len(popular)), popular, strict=True):
            with col, st.container(border=True):
                st.markdown(f'<p class="cm-title">{esc(pkg.name)}</p>', unsafe_allow_html=True)
                names = ", ".join(t.name.split(" (")[0] for t in pkg.tests)
                st.markdown(f'<p class="cm-muted">{esc(names)}</p>', unsafe_allow_html=True)
                st.markdown(price_html(pkg.price, pkg.mrp, pkg.discount_pct), unsafe_allow_html=True)
        if "tests" in PAGES:
            st.page_link(PAGES["tests"], label="See all tests and panels")


def _fasting_chip(hours: int) -> tuple[str, str]:
    return ("No fasting", "green") if hours == 0 else (f"Fast {hours} h", "gold")


def _turnaround(hours: int) -> str:
    return "Report in 24 h" if hours <= 24 else f"Report in {hours // 24} days"


def page_tests() -> None:
    st.title("Tests and panels")
    advisory()
    st.info("Online booking (cart, slots and payment) opens in the next release. "
            "For now you can check coverage, create an account and explore the menu.")
    user = current_user()
    with session_scope() as db:
        categories = list_categories(db)
    c1, c2, c3 = st.columns([3, 2, 2])
    query = c1.text_input("Search", placeholder="Prostate, CA 125, liver...")
    category = c2.selectbox("Organ or site", ["All"] + categories)
    no_fast = c3.toggle("No fasting needed")
    tab_pkg, tab_tests = st.tabs(["Panels", "Individual tests"])

    with tab_pkg:
        default = {"Male": 1, "Female": 2}.get(user.sex if user else "", 0)
        who = st.radio("Show panels for", ["Everyone", "Men", "Women"], index=default, horizontal=True)
        with session_scope() as db:
            packages = list_packages(db, {"Men": "male", "Women": "female"}.get(who))
        if query:
            q = query.lower()
            packages = [p for p in packages if q in p.name.lower() or q in p.description.lower()
                        or any(q in t.name.lower() or q in t.category.lower() or q in t.code.lower() for t in p.tests)]
        if no_fast:
            packages = [p for p in packages if p.fasting_hours == 0]
        if category != "All":
            packages = [p for p in packages if any(t.category == category for t in p.tests)]
        if not packages:
            st.write("No panels match these filters. Clear the search or switch the audience.")
        for p in packages:
            with st.container(border=True):
                st.markdown(f'<p class="cm-title">{esc(p.name)}</p>', unsafe_allow_html=True)
                chips([(f"{len(p.tests)} tests", ""), _fasting_chip(p.fasting_hours), (_turnaround(p.tat_hours), "")])
                st.write(p.description)
                st.markdown(price_html(p.price, p.mrp, p.discount_pct), unsafe_allow_html=True)
                with st.expander("Tests included"):
                    for t in p.tests:
                        st.markdown(f"- **{t.name}**: {t.category}")

    with tab_tests:
        with session_scope() as db:
            tests = search_tests(db, query, None if category == "All" else category, no_fast)
        if not tests:
            st.write("No tests match these filters. Try a different organ or clear the search.")
        for t in tests:
            with st.container(border=True):
                st.markdown(f'<p class="cm-title">{esc(t.name)}</p>', unsafe_allow_html=True)
                items = [(t.category, ""), (t.sample_type, ""), _fasting_chip(t.fasting_hours),
                         (_turnaround(t.tat_hours), "")]
                chips([("Popular", "gold")] + items if t.popular else items)
                st.write(t.description)
                st.markdown(price_html(t.price, t.mrp, t.discount_pct), unsafe_allow_html=True)
                with st.expander("Preparation and what can affect the result"):
                    st.markdown(f"**Before the test.** {t.prep_notes}")
                    st.markdown(f"**Can affect the result.** {t.interference_notes}")


def page_login() -> None:
    """Pincode + phone -> OTP -> (new users) profile and consent."""
    user = current_user()
    if is_authenticated(user):
        st.success("You're signed in.")
        return
    st.title("Sign in or create your account")
    step = "profile" if user else st.session_state.get("auth_step", "phone")  # unfinished profile must finish
    {"phone": _step_phone, "otp": _step_otp, "profile": _step_profile}[step]()


def _step_phone() -> None:
    st.write("Enter your pincode and mobile number. We'll text you a one-time code. No password needed.")
    sync_pincode_input("login_pincode")
    with st.form("phone_form"):
        pincode = st.text_input("Pincode", key="login_pincode", max_chars=6)
        phone = st.text_input("Mobile number", max_chars=16, placeholder="98450 12345",
                              help="Indian mobile numbers only (+91).")
        go = st.form_submit_button("Send code", type="primary")
    if not go:
        return
    try:
        with session_scope() as db:
            found = check_pincode(db, pincode)
            issued = request_otp(db, phone)
    except RateLimited as exc:
        st.warning(str(exc))
        return
    except ServiceError as exc:
        st.error(str(exc))
        return
    set_pincode_info(found, "login_pincode")
    st.session_state.update(auth_step="otp", auth_phone=issued.phone, auth_dev_otp=issued.dev_otp)
    st.rerun()


def _step_otp() -> None:
    phone = st.session_state["auth_phone"]
    st.write(f"We sent a 6-digit code to **{mask_phone(phone)}**. It stays valid for 5 minutes.")
    if st.session_state.get("auth_dev_otp"):
        st.info(f"Development mode: your code is **{st.session_state['auth_dev_otp']}**")
    with st.form("otp_form"):
        code = st.text_input("6-digit code", max_chars=6, autocomplete="one-time-code")
        verify = st.form_submit_button("Verify and continue", type="primary")
    if verify:
        try:
            with session_scope() as db:
                result = verify_otp(db, phone, code)
        except ServiceError as exc:
            st.error(str(exc))
        else:
            st.session_state["session_token"] = result.token
            if result.user.profile_complete:
                clear_auth_flow()
            else:
                st.session_state["auth_step"] = "profile"
            st.rerun()
    c1, c2 = st.columns(2)
    if c1.button("Resend code"):
        try:
            with session_scope() as db:
                st.session_state["auth_dev_otp"] = request_otp(db, phone).dev_otp
            st.rerun()
        except ServiceError as exc:
            st.warning(str(exc))
    if c2.button("Use a different number"):
        clear_auth_flow()
        st.rerun()


def _step_profile() -> None:
    st.write("One last step. This is the information your lab report will carry.")
    user = current_user()
    sync_pincode_input("profile_pincode")
    with st.form("profile_form"):
        name = st.text_input("Full name", max_chars=120)
        email = st.text_input("Email (optional)", max_chars=254, help="We'll email report links here if you add one.")
        dob = st.date_input("Date of birth", value=date(1990, 1, 1), min_value=date(1900, 1, 1),
                            max_value=date.today(), format="DD/MM/YYYY")
        sex = st.radio("Sex", SEX_OPTIONS, horizontal=True, help="Reference ranges for some markers differ by sex.")
        pincode = st.text_input("Home pincode", key="profile_pincode", max_chars=6)
        st.markdown("**Consent**")
        terms = st.checkbox("I agree to the Terms of Service and Privacy Policy.")
        health = st.checkbox("I consent to this service collecting and processing my health information "
                             "(test orders and reports) to book tests and deliver results to me.")
        marketing = st.checkbox("Send me health reminders and offers (optional).")
        done = st.form_submit_button("Create account", type="primary")
    if not done or user is None:
        return
    try:
        with session_scope() as db:
            complete_profile(db, user.user_id, name=name, email=email, dob=dob, sex=sex, pincode=pincode,
                             accept_terms=terms, accept_health_data=health, marketing=marketing)
    except ServiceError as exc:
        st.error(str(exc))
        return
    clear_auth_flow()
    st.rerun()


def page_account() -> None:
    user = current_user()
    if user is None:
        st.warning("Please sign in first.")
        return
    st.title("My account")
    st.markdown(f"**Mobile:** {mask_phone(user.phone)}")
    with st.form("profile_edit"):
        name = st.text_input("Full name", value=user.name or "", max_chars=120)
        email = st.text_input("Email (optional)", value=user.email or "", max_chars=254)
        dob = st.date_input("Date of birth", value=user.dob or date(1990, 1, 1), min_value=date(1900, 1, 1),
                            max_value=date.today(), format="DD/MM/YYYY")
        sex = st.radio("Sex", SEX_OPTIONS, index=SEX_OPTIONS.index(user.sex) if user.sex in SEX_OPTIONS else 0,
                       horizontal=True)
        pincode = st.text_input("Home pincode", value=user.home_pincode or "", max_chars=6)
        save = st.form_submit_button("Save changes", type="primary")
    if save:
        try:
            with session_scope() as db:
                update_profile(db, user.user_id, name=name, email=email, dob=dob, sex=sex, pincode=pincode)
            st.success("Changes saved.")
        except ServiceError as exc:
            st.error(str(exc))
    st.divider()
    if st.button("Sign out"):
        with session_scope() as db:
            logout(db, st.session_state.get("session_token"))
        st.session_state.pop("session_token", None)
        clear_auth_flow()
        st.rerun()


def render_header() -> None:
    left, mid, _ = st.columns([3, 3, 2], vertical_alignment="center")
    left.markdown(f'<p class="cm-brand">{esc(BRAND)}<span>.</span></p>', unsafe_allow_html=True)
    info = get_pincode_info()
    with mid.popover(f"Pincode {info.pincode}" if info else "Set pincode", icon=":material/location_on:"):
        sync_pincode_input("header_pincode")
        with st.form("header_pincode_form"):
            pin = st.text_input("Pincode", key="header_pincode", max_chars=6)
            if st.form_submit_button("Check"):
                try:
                    with session_scope() as db:
                        set_pincode_info(check_pincode(db, pin), "header_pincode")
                    st.rerun()
                except ServiceError as exc:
                    st.error(str(exc))
        if info:
            pincode_result(info, key="header")


# ======================================================================================
# 7. ENTRY POINT
# ======================================================================================

@st.cache_resource(show_spinner=False)
def bootstrap() -> str | None:
    """Validate config, create tables, seed data. Returns an error message if startup is unsafe."""
    try:
        get_settings()
    except ConfigError as exc:
        return str(exc)
    init_engine()
    Base.metadata.create_all(_engine)
    with session_scope() as db:
        seed_all(db)
    return None


def main() -> None:
    st.set_page_config(page_title=f"{BRAND}: cancer marker tests at home", page_icon="🩺", layout="centered")
    st.markdown(CSS, unsafe_allow_html=True)
    error = bootstrap()
    if error:
        st.error(error)
        st.stop()

    authenticated = is_authenticated(current_user())
    pages = {
        "home": st.Page(page_home, title="Home", icon=":material/home:", url_path="home", default=True),
        "tests": st.Page(page_tests, title="Tests", icon=":material/biotech:", url_path="tests"),
    }
    if authenticated:
        pages["account"] = st.Page(page_account, title="My account", icon=":material/person:", url_path="account")
    else:
        pages["login"] = st.Page(page_login, title="Sign in", icon=":material/login:", url_path="sign-in")
    PAGES.clear()
    PAGES.update(pages)

    render_header()
    try:
        nav = st.navigation(list(pages.values()), position="top")
    except TypeError:  # older Streamlit without top navigation
        nav = st.navigation(list(pages.values()))
    nav.run()
    st.markdown(f'<div class="cm-footer">{esc(BRAND)} is a demonstration build. Prices and turnaround times are '
                "illustrative. Reports must come from an accredited laboratory.</div>", unsafe_allow_html=True)


if __name__ == "__main__":
    main()
