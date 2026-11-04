"""MarkerHome: cancer marker test booking with an admin dashboard.

Single-file Streamlit app.   Run:  streamlit run app.py

Customer side : pincode check, phone+OTP sign-in, catalogue, cart, family members, addresses, slot booking,
                coupons, orders (reschedule / cancel / report download).
Admin side    : overview, orders (assign / status / payment / reports), run sheet, catalogue, locations,
                slots, collectors, coupons, customers, audit log.

Sections:  1 Config   2 Errors/validators/security   3 Database models   4 Seed data
           5 Services (SMS, auth, pincode, catalogue, booking, admin)   6 UI (customer + admin pages)
           7 Entry point

Status: demo build. Online payment is a DEMO gateway (disabled when APP_ENV=production).
Prices, turnaround times, pincodes, slots and collectors seeded below are ILLUSTRATIVE.
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
import csv
import io
from collections import Counter
from datetime import date, datetime, time, timedelta, timezone
from functools import lru_cache
from pathlib import Path
from typing import Iterator, Literal

import streamlit as st
from sqlalchemy import (Boolean, Column, Date, DateTime, ForeignKey, Index, Integer, LargeBinary, String, Table,
                        Text, UniqueConstraint, create_engine, event, func, inspect, or_, select, update)
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
    admin_phones: tuple[str, ...] = ()        # numbers that are promoted to admin when they sign in
    free_collection_threshold: int = 999      # collection fee is waived at or above this subtotal (Rs)
    booking_cutoff_hours: int = 2             # no booking / cancelling / rescheduling closer than this to the slot
    booking_window_days: int = 7              # how far ahead a slot can be booked
    payment_hold_minutes: int = 15            # unpaid online orders release their slot after this
    max_report_mb: int = 5

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
        if not self.admin_phones:
            problems.append("ADMIN_PHONES must list at least one admin mobile number")
        if problems:
            raise ConfigError("Unsafe production configuration: " + "; ".join(problems))


@lru_cache(maxsize=1)
def get_settings() -> Settings:
    d = Settings()
    app_env = (_env("APP_ENV", "dev") or "dev").lower()
    provider = (_env("SMS_PROVIDER", "console") or "console").lower()
    show_default = app_env != "production" and provider == "console"
    flag = _env("SHOW_DEV_OTP")
    raw_admins = _env("ADMIN_PHONES")
    if raw_admins is None:  # dev convenience only: sign in as 9999999999 to reach the admin pages
        admins = ("+919999999999",) if app_env != "production" else ()
    else:
        admins = tuple(normalize_phone(p) for p in raw_admins.split(",") if p.strip())
    s = Settings(
        app_env=app_env,
        database_url=_env("DATABASE_URL", d.database_url),
        secret_key=_env("SECRET_KEY", d.secret_key),
        sms_provider=provider,
        msg91_auth_key=_env("MSG91_AUTH_KEY", "") or "",
        msg91_template_id=_env("MSG91_TEMPLATE_ID", "") or "",
        admin_phones=admins,
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


def _clock() -> datetime:
    """Column default that looks utcnow up at call time (so tests can control time)."""
    return utcnow()


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


def validate_text(raw: str, label: str, *, min_len: int = 1, max_len: int = 200) -> str:
    text = re.sub(r"\s+", " ", (raw or "").strip())
    if not (min_len <= len(text) <= max_len):
        raise ValidationError(f"{label} must be {min_len} to {max_len} characters.")
    return text


def validate_code(raw: str, label: str = "Code") -> str:
    code = (raw or "").strip().upper()
    if not re.fullmatch(r"[A-Z0-9][A-Z0-9\-]{1,29}", code):
        raise ValidationError(f"{label} must be 2 to 30 characters: letters, digits and hyphens.")
    return code


def validate_int(value, label: str, *, minimum: int = 0, maximum: int = 10_000_000) -> int:
    try:
        number = int(value)
    except (TypeError, ValueError):
        raise ValidationError(f"{label} must be a whole number.") from None
    if not (minimum <= number <= maximum):
        raise ValidationError(f"{label} must be between {minimum:,} and {maximum:,}.")
    return number


def validate_hhmm(raw: str) -> str:
    try:
        return time.fromisoformat(raw.strip()).strftime("%H:%M")
    except (ValueError, AttributeError):
        raise ValidationError("Enter times as HH:MM, for example 06:00.") from None


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
    created_at: Mapped[datetime] = mapped_column(DateTime, default=_clock)
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
    active: Mapped[bool] = mapped_column(Boolean, default=True)
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
    created_at: Mapped[datetime] = mapped_column(DateTime, default=_clock)


class UserSession(Base):
    __tablename__ = "user_sessions"
    id: Mapped[int] = mapped_column(primary_key=True)
    token_hash: Mapped[str] = mapped_column(String(64), unique=True, index=True)
    user_id: Mapped[int] = mapped_column(ForeignKey("users.id", ondelete="CASCADE"), index=True)
    created_at: Mapped[datetime] = mapped_column(DateTime, default=_clock)
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
    created_at: Mapped[datetime] = mapped_column(DateTime, default=_clock)


class AuditLog(Base):
    __tablename__ = "audit_log"
    id: Mapped[int] = mapped_column(primary_key=True)
    actor_id: Mapped[int | None] = mapped_column(Integer)
    action: Mapped[str] = mapped_column(String(60), index=True)
    entity: Mapped[str | None] = mapped_column(String(40))
    entity_id: Mapped[str | None] = mapped_column(String(64))  # never a raw phone number
    created_at: Mapped[datetime] = mapped_column(DateTime, default=_clock)


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
    created_at: Mapped[datetime] = mapped_column(DateTime, default=_clock)


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


class Address(Base):
    __tablename__ = "addresses"
    id: Mapped[int] = mapped_column(primary_key=True)
    user_id: Mapped[int] = mapped_column(ForeignKey("users.id", ondelete="CASCADE"), index=True)
    label: Mapped[str] = mapped_column(String(30))
    line1: Mapped[str] = mapped_column(String(200))
    landmark: Mapped[str | None] = mapped_column(String(120))
    pincode: Mapped[str] = mapped_column(String(6))
    active: Mapped[bool] = mapped_column(Boolean, default=True)  # soft delete: old orders keep a snapshot anyway
    created_at: Mapped[datetime] = mapped_column(DateTime, default=_clock)


class Slot(Base):
    """A collection window for a city. `booked` is changed only by atomic UPDATEs (see create_order)."""
    __tablename__ = "slots"
    __table_args__ = (UniqueConstraint("city", "day", "start"),)
    id: Mapped[int] = mapped_column(primary_key=True)
    city: Mapped[str] = mapped_column(String(80), index=True)
    day: Mapped[date] = mapped_column(Date, index=True)  # local (IST) calendar day
    start: Mapped[str] = mapped_column(String(5))        # "HH:MM"
    end: Mapped[str] = mapped_column(String(5))
    capacity: Mapped[int] = mapped_column(Integer)
    booked: Mapped[int] = mapped_column(Integer, default=0)
    active: Mapped[bool] = mapped_column(Boolean, default=True)

    @property
    def start_dt(self) -> datetime:
        return datetime.combine(self.day, time.fromisoformat(self.start))


class Phlebotomist(Base):
    __tablename__ = "phlebotomists"
    id: Mapped[int] = mapped_column(primary_key=True)
    name: Mapped[str] = mapped_column(String(120))
    phone: Mapped[str] = mapped_column(String(13))
    city: Mapped[str] = mapped_column(String(80), index=True)
    active: Mapped[bool] = mapped_column(Boolean, default=True)


class Coupon(Base):
    __tablename__ = "coupons"
    id: Mapped[int] = mapped_column(primary_key=True)
    code: Mapped[str] = mapped_column(String(30), unique=True, index=True)
    kind: Mapped[str] = mapped_column(String(10))  # percent | flat
    value: Mapped[int] = mapped_column(Integer)
    min_order: Mapped[int] = mapped_column(Integer, default=0)
    max_discount: Mapped[int | None] = mapped_column(Integer)  # cap for percent coupons
    valid_from: Mapped[date | None] = mapped_column(Date)
    valid_to: Mapped[date | None] = mapped_column(Date)
    usage_limit: Mapped[int | None] = mapped_column(Integer)
    used_count: Mapped[int] = mapped_column(Integer, default=0)
    per_user_limit: Mapped[int] = mapped_column(Integer, default=1)
    active: Mapped[bool] = mapped_column(Boolean, default=True)


class Order(Base):
    __tablename__ = "orders"
    id: Mapped[int] = mapped_column(primary_key=True)
    order_no: Mapped[str] = mapped_column(String(20), unique=True, index=True)
    user_id: Mapped[int] = mapped_column(ForeignKey("users.id"), index=True)
    status: Mapped[str] = mapped_column(String(20), default="booked", index=True)
    subtotal: Mapped[int] = mapped_column(Integer)
    discount: Mapped[int] = mapped_column(Integer, default=0)
    collection_fee: Mapped[int] = mapped_column(Integer, default=0)
    total: Mapped[int] = mapped_column(Integer)
    coupon_code: Mapped[str | None] = mapped_column(String(30))
    payment_method: Mapped[str] = mapped_column(String(10))   # online | cod
    payment_status: Mapped[str] = mapped_column(String(10))   # pending | paid | cod | refunded | void
    payment_ref: Mapped[str | None] = mapped_column(String(40))
    idempotency_key: Mapped[str | None] = mapped_column(String(40), unique=True)
    slot_id: Mapped[int] = mapped_column(ForeignKey("slots.id"), index=True)
    phlebotomist_id: Mapped[int | None] = mapped_column(ForeignKey("phlebotomists.id"))
    addr_label: Mapped[str] = mapped_column(String(30))       # address is SNAPSHOTTED: later edits don't rewrite history
    addr_line: Mapped[str] = mapped_column(String(320))
    addr_pincode: Mapped[str] = mapped_column(String(6))
    city: Mapped[str] = mapped_column(String(80), index=True)
    cancel_reason: Mapped[str | None] = mapped_column(String(200))
    created_at: Mapped[datetime] = mapped_column(DateTime, default=_clock, index=True)
    updated_at: Mapped[datetime] = mapped_column(DateTime, default=_clock)

    user: Mapped[User] = relationship()
    slot: Mapped[Slot] = relationship()
    phlebotomist: Mapped[Phlebotomist | None] = relationship()
    items: Mapped[list["OrderItem"]] = relationship(cascade="all, delete-orphan", order_by="OrderItem.id")
    events: Mapped[list["OrderEvent"]] = relationship(cascade="all, delete-orphan", order_by="OrderEvent.id")


class OrderItem(Base):
    __tablename__ = "order_items"
    id: Mapped[int] = mapped_column(primary_key=True)
    order_id: Mapped[int] = mapped_column(ForeignKey("orders.id", ondelete="CASCADE"), index=True)
    patient_id: Mapped[int] = mapped_column(ForeignKey("patients.id"))
    item_type: Mapped[str] = mapped_column(String(10))  # test | package
    code: Mapped[str] = mapped_column(String(30))
    name: Mapped[str] = mapped_column(String(120))      # snapshot
    price: Mapped[int] = mapped_column(Integer)         # snapshot
    mrp: Mapped[int] = mapped_column(Integer)
    patient: Mapped[Patient] = relationship()


class OrderEvent(Base):
    __tablename__ = "order_events"
    id: Mapped[int] = mapped_column(primary_key=True)
    order_id: Mapped[int] = mapped_column(ForeignKey("orders.id", ondelete="CASCADE"), index=True)
    status: Mapped[str] = mapped_column(String(20))
    note: Mapped[str | None] = mapped_column(String(300))
    actor_id: Mapped[int | None] = mapped_column(Integer)  # None = system
    created_at: Mapped[datetime] = mapped_column(DateTime, default=_clock)


class Report(Base):
    """PDF kept in the database for this demo. In production use private object storage + signed URLs."""
    __tablename__ = "reports"
    id: Mapped[int] = mapped_column(primary_key=True)
    order_id: Mapped[int] = mapped_column(ForeignKey("orders.id", ondelete="CASCADE"), index=True)
    filename: Mapped[str] = mapped_column(String(120))
    content: Mapped[bytes] = mapped_column(LargeBinary)
    uploaded_by: Mapped[int | None] = mapped_column(Integer)
    uploaded_at: Mapped[datetime] = mapped_column(DateTime, default=_clock)


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


DEMO_WINDOWS = (("06:00", "08:00"), ("08:00", "10:00"), ("10:00", "12:00"))


def seed_demo_data(db: Session) -> None:
    """DEV ONLY (skipped when APP_ENV=production): rolling slots for the next 8 days, two collectors per active
    city and one coupon, so the demo works out of the box. Idempotent. In production admins create these."""
    cities = [c for (c,) in db.execute(select(ServiceablePincode.city).where(ServiceablePincode.active.is_(True)).distinct())]
    today = local_now().date()
    for city in cities:
        for offset in range(0, 9):
            for a, b in DEMO_WINDOWS:
                day = today + timedelta(days=offset)
                if not db.scalar(select(Slot.id).where(Slot.city == city, Slot.day == day, Slot.start == a)):
                    db.add(Slot(city=city, day=day, start=a, end=b, capacity=6))
        if not db.scalar(select(Phlebotomist.id).where(Phlebotomist.city == city)):
            db.add(Phlebotomist(name=f"Demo Collector A ({city})", phone="+919000000001", city=city))
            db.add(Phlebotomist(name=f"Demo Collector B ({city})", phone="+919000000002", city=city))
    if not db.scalar(select(Coupon.id).where(Coupon.code == "WELCOME10")):
        db.add(Coupon(code="WELCOME10", kind="percent", value=10, min_order=500, max_discount=200, per_user_limit=1))
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
        # print() so it shows in the terminal / Streamlit Cloud logs even without logging configuration
        print(f"[DEV OTP] {mask_phone(phone)}: {otp} (valid {ttl_minutes} min)", flush=True)


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
    # Never put an admin's code on screen, even in dev mode: otherwise anyone could request it and sign in as admin.
    # Admins read the code from the server log (ConsoleSms) or receive it by SMS.
    show = s.show_dev_otp and phone not in s.admin_phones
    return OtpIssued(phone, now + timedelta(seconds=s.otp_ttl_seconds), otp if show else None)


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
    if phone in s.admin_phones and user.role != "admin":  # admins are listed in ADMIN_PHONES (config, not UI)
        user.role = "admin"
        audit(db, "admin_granted_by_config", actor_id=user.id, entity="user", entity_id=user.id)
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


# ---- Booking: addresses, family members, slots, pricing, orders ----------------------

IST = timedelta(hours=5, minutes=30)


def local_now() -> datetime:
    """Current India time as a naive datetime. Slots are stored in local time."""
    return utcnow() + IST


ORDER_STATUSES = ("booked", "assigned", "collected", "in_lab", "report_ready", "cancelled")
STATUS_LABELS = {"booked": "Booked", "assigned": "Collector assigned", "collected": "Sample collected",
                 "in_lab": "At the lab", "report_ready": "Report ready", "cancelled": "Cancelled"}
TRANSITIONS = {"booked": {"assigned", "cancelled"}, "assigned": {"collected", "cancelled"},
               "collected": {"in_lab", "cancelled"}, "in_lab": {"report_ready", "cancelled"},
               "report_ready": set(), "cancelled": set()}
CUSTOMER_CANCELLABLE = {"booked", "assigned"}
RELATIONS = ("self", "spouse", "parent", "child", "sibling", "other")


@dataclass(frozen=True)
class AddressDTO:
    id: int
    label: str
    line1: str
    landmark: str | None
    pincode: str

    @property
    def text(self) -> str:
        return ", ".join(p for p in (self.line1, self.landmark, self.pincode) if p)


@dataclass(frozen=True)
class PatientDTO:
    id: int
    name: str
    dob: date
    sex: str
    relation: str


@dataclass(frozen=True)
class SlotDTO:
    id: int
    city: str
    day: date
    start: str
    end: str
    capacity: int
    booked: int
    active: bool

    @property
    def remaining(self) -> int:
        return max(self.capacity - self.booked, 0)

    @property
    def label(self) -> str:
        return f"{self.start} to {self.end}"


@dataclass(frozen=True)
class OrderItemDTO:
    patient_id: int
    patient_name: str
    item_type: str
    code: str
    name: str
    price: int
    mrp: int


@dataclass(frozen=True)
class OrderEventDTO:
    status: str
    note: str | None
    created_at: datetime  # local time
    actor_id: int | None


@dataclass(frozen=True)
class OrderDTO:
    order_no: str
    user_id: int
    customer_name: str | None
    customer_phone: str
    status: str
    subtotal: int
    discount: int
    collection_fee: int
    total: int
    coupon_code: str | None
    payment_method: str
    payment_status: str
    payment_ref: str | None
    slot: SlotDTO
    address_label: str
    address_text: str
    address_pincode: str
    city: str
    phlebotomist_id: int | None
    phlebotomist_name: str | None
    items: list[OrderItemDTO]
    events: list[OrderEventDTO]
    created_at: datetime  # local time
    cancel_reason: str | None
    has_report: bool

    @property
    def status_label(self) -> str:
        return STATUS_LABELS.get(self.status, self.status)


@dataclass(frozen=True)
class QuoteLine:
    item_type: str
    code: str
    name: str
    price: int
    mrp: int
    patient_id: int
    patient_name: str


@dataclass(frozen=True)
class Quote:
    lines: list[QuoteLine]
    subtotal: int
    discount: int
    collection_fee: int
    total: int
    coupon_code: str | None
    city: str | None


def _slot_dto(sl: Slot) -> SlotDTO:
    return SlotDTO(sl.id, sl.city, sl.day, sl.start, sl.end, sl.capacity, sl.booked, sl.active)


def _addr_dto(a: Address) -> AddressDTO:
    return AddressDTO(a.id, a.label, a.line1, a.landmark, a.pincode)


def _patient_dto(p: Patient) -> PatientDTO:
    return PatientDTO(p.id, p.name, p.dob, p.sex, p.relation)


def _order_dto(o: Order, has_report: bool) -> OrderDTO:
    return OrderDTO(
        order_no=o.order_no, user_id=o.user_id, customer_name=o.user.name, customer_phone=o.user.phone,
        status=o.status, subtotal=o.subtotal, discount=o.discount, collection_fee=o.collection_fee, total=o.total,
        coupon_code=o.coupon_code, payment_method=o.payment_method, payment_status=o.payment_status,
        payment_ref=o.payment_ref, slot=_slot_dto(o.slot), address_label=o.addr_label, address_text=o.addr_line,
        address_pincode=o.addr_pincode, city=o.city, phlebotomist_id=o.phlebotomist_id,
        phlebotomist_name=o.phlebotomist.name if o.phlebotomist else None,
        items=[OrderItemDTO(i.patient_id, i.patient.name, i.item_type, i.code, i.name, i.price, i.mrp)
               for i in o.items],
        events=[OrderEventDTO(e.status, e.note, e.created_at + IST, e.actor_id) for e in o.events],
        created_at=o.created_at + IST, cancel_reason=o.cancel_reason, has_report=has_report)


def _has_report(db: Session, order_id: int) -> bool:
    return db.scalar(select(func.count()).select_from(Report).where(Report.order_id == order_id)) > 0


def _event(db: Session, order: Order, status: str, note: str | None = None, actor_id: int | None = None) -> None:
    order.updated_at = utcnow()
    order.events.append(OrderEvent(status=status, note=note, actor_id=actor_id))


# addresses -------------------------------------------------------------------------

def list_addresses(db: Session, user_id: int) -> list[AddressDTO]:
    return [_addr_dto(a) for a in db.scalars(select(Address).where(Address.user_id == user_id, Address.active.is_(True))
                                             .order_by(Address.id))]


def add_address(db: Session, user_id: int, *, label: str, line1: str, landmark: str | None, pincode: str) -> AddressDTO:
    if len(list_addresses(db, user_id)) >= 10:
        raise ValidationError("You can save up to 10 addresses. Remove one first.")
    a = Address(user_id=user_id, label=validate_text(label, "Address label", max_len=30),
                line1=validate_text(line1, "Address", min_len=8, max_len=200),
                landmark=validate_text(landmark, "Landmark", min_len=0, max_len=120) or None if landmark else None,
                pincode=validate_pincode(pincode))
    db.add(a)
    db.commit()
    return _addr_dto(a)


def delete_address(db: Session, user_id: int, address_id: int) -> None:
    a = db.get(Address, address_id)
    if a is None or a.user_id != user_id:
        raise ServiceError("Address not found.")
    a.active = False
    db.commit()


# family members --------------------------------------------------------------------

def list_patients(db: Session, user_id: int) -> list[PatientDTO]:
    rows = db.scalars(select(Patient).where(Patient.user_id == user_id, Patient.active.is_(True)).order_by(Patient.id))
    return [_patient_dto(p) for p in rows]


def add_patient(db: Session, user_id: int, *, name: str, dob: date | None, sex: str, relation: str) -> PatientDTO:
    if relation not in RELATIONS or relation == "self":
        raise ValidationError("Choose how this person is related to you.")
    if len(list_patients(db, user_id)) >= 8:
        raise ValidationError("You can add up to 8 people. Remove one first.")
    p = Patient(user_id=user_id, name=validate_name(name), dob=validate_dob(dob), sex=validate_sex(sex),
                relation=relation)
    db.add(p)
    db.commit()
    return _patient_dto(p)


def delete_patient(db: Session, user_id: int, patient_id: int) -> None:
    p = db.get(Patient, patient_id)
    if p is None or p.user_id != user_id:
        raise ServiceError("Person not found.")
    if p.relation == "self":
        raise ServiceError("You can't remove yourself. Edit your details in My account instead.")
    p.active = False  # soft delete: past orders still point at this patient
    db.commit()


# slots -----------------------------------------------------------------------------

def _slot_open(sl: Slot, s: Settings) -> bool:
    """Active, not too soon, not too far ahead. (Capacity is checked separately.)"""
    now = local_now()
    return (sl.active and sl.start_dt >= now + timedelta(hours=s.booking_cutoff_hours)
            and sl.day <= now.date() + timedelta(days=s.booking_window_days))


def bookable_slots(db: Session, city: str, *, settings: Settings | None = None) -> list[SlotDTO]:
    s = settings or get_settings()
    rows = db.scalars(select(Slot).where(Slot.city == city, Slot.active.is_(True), Slot.day >= local_now().date(),
                                         Slot.booked < Slot.capacity).order_by(Slot.day, Slot.start))
    return [_slot_dto(sl) for sl in rows if _slot_open(sl, s)]


# pricing ---------------------------------------------------------------------------

def _resolve_items(db: Session, user_id: int, items: list[dict]) -> list[QuoteLine]:
    if not items:
        raise ValidationError("Your cart is empty.")
    if len(items) > 20:
        raise ValidationError("A single booking can include up to 20 items.")
    patients = {p.id: p for p in db.scalars(select(Patient).where(Patient.user_id == user_id, Patient.active.is_(True)))}
    lines: list[QuoteLine] = []
    covered: dict[tuple[int, str], str] = {}
    for it in items:
        patient = patients.get(it.get("patient_id"))
        if patient is None:
            raise ValidationError("Choose who each test is for.")
        if it.get("type") == "test":
            t = db.scalar(select(Test).where(Test.code == it.get("code"), Test.active.is_(True)))
            if t is None:
                raise ValidationError("A test in your cart is no longer available. Remove it and try again.")
            codes, name, price, mrp = [t.code], t.name, t.price, t.mrp
        elif it.get("type") == "package":
            p = db.scalar(select(Package).options(selectinload(Package.tests))
                          .where(Package.code == it.get("code"), Package.active.is_(True)))
            if p is None:
                raise ValidationError("A panel in your cart is no longer available. Remove it and try again.")
            if p.audience in ("male", "female") and patient.sex in ("Male", "Female") and patient.sex.lower() != p.audience:
                raise ValidationError(f"{p.name} is designed for {p.audience} patients, but {patient.name} is "
                                      f"{patient.sex.lower()}. Choose another panel or person.")
            codes, name, price, mrp = [t.code for t in p.tests], p.name, p.price, p.mrp
        else:
            raise ValidationError("Unknown item in cart.")
        for c in codes:  # never charge twice for the same marker for the same person
            if (patient.id, c) in covered:
                raise ValidationError(f"{c} is already in the cart for {patient.name} (in {covered[(patient.id, c)]}). "
                                      "Remove the duplicate.")
            covered[(patient.id, c)] = name
        lines.append(QuoteLine(it["type"], it["code"], name, price, mrp, patient.id, patient.name))
    return lines


def validate_coupon(db: Session, code: str, user_id: int, subtotal: int) -> tuple[Coupon, int]:
    c = db.scalar(select(Coupon).where(Coupon.code == (code or "").strip().upper()))
    if c is None or not c.active:
        raise ValidationError("That coupon code isn't valid.")
    today = local_now().date()
    if c.valid_from and today < c.valid_from:
        raise ValidationError("That coupon isn't active yet.")
    if c.valid_to and today > c.valid_to:
        raise ValidationError("That coupon has expired.")
    if c.usage_limit is not None and c.used_count >= c.usage_limit:
        raise ValidationError("That coupon has been fully redeemed.")
    if subtotal < c.min_order:
        raise ValidationError(f"This coupon needs a minimum order of ₹{c.min_order:,}.")
    used = db.scalar(select(func.count()).select_from(Order).where(
        Order.user_id == user_id, Order.coupon_code == c.code, Order.status != "cancelled")) or 0
    if used >= c.per_user_limit:
        raise ValidationError("You have already used this coupon.")
    discount = c.value if c.kind == "flat" else subtotal * c.value // 100
    if c.max_discount is not None:
        discount = min(discount, c.max_discount)
    return c, max(min(discount, subtotal), 0)


def build_quote(db: Session, user_id: int, items: list[dict], *, pincode: str | None = None,
                coupon_code: str | None = None, settings: Settings | None = None) -> Quote:
    """Single source of price truth: used for the on-screen summary AND when the order is created."""
    s = settings or get_settings()
    lines = _resolve_items(db, user_id, items)
    subtotal = sum(l.price for l in lines)
    discount, applied = 0, None
    if coupon_code:
        c, discount = validate_coupon(db, coupon_code, user_id, subtotal)
        applied = c.code
    fee, city = 0, None
    if pincode:
        info = check_pincode(db, pincode)
        if not info.serviceable:
            raise ValidationError(f"We can't collect samples at {info.pincode} yet.")
        city = info.city
        fee = 0 if subtotal >= s.free_collection_threshold else info.collection_fee
    return Quote(lines, subtotal, discount, fee, subtotal - discount + fee, applied, city)


# orders ----------------------------------------------------------------------------

def _new_order_no(db: Session) -> str:
    for _ in range(10):
        no = "MH" + local_now().strftime("%y%m%d") + "".join(secrets.choice("ABCDEFGHJKLMNPQRSTUVWXYZ23456789") for _ in range(5))
        if db.scalar(select(Order.id).where(Order.order_no == no)) is None:
            return no
    raise ServiceError("Could not generate an order number. Please try again.")


def create_order(db: Session, user_id: int, *, items: list[dict], address_id: int, slot_id: int,
                 payment_method: str, coupon_code: str | None = None, idempotency_key: str | None = None,
                 settings: Settings | None = None) -> OrderDTO:
    s = settings or get_settings()
    if idempotency_key:  # a double-click or retry returns the same order instead of booking twice
        prior = db.scalar(select(Order).where(Order.idempotency_key == idempotency_key, Order.user_id == user_id))
        if prior is not None:
            return _order_dto(prior, _has_report(db, prior.id))
    if payment_method not in ("online", "cod"):
        raise ValidationError("Choose a payment method.")
    if payment_method == "online" and s.app_env == "production":
        raise ValidationError("Online payment isn't available yet. Choose pay on collection.")
    user = db.get(User, user_id)
    if user is None or not user.is_active or not user.profile_complete:
        raise ServiceError("Please complete your profile before booking.")
    addr = db.get(Address, address_id)
    if addr is None or addr.user_id != user_id or not addr.active:
        raise ValidationError("Choose a collection address.")
    quote = build_quote(db, user_id, items, pincode=addr.pincode, coupon_code=coupon_code, settings=s)
    slot = db.get(Slot, slot_id)
    if slot is None or slot.city != quote.city or not _slot_open(slot, s):
        raise ValidationError("That time slot isn't available. Please pick another.")

    try:
        got = db.execute(update(Slot).where(Slot.id == slot_id, Slot.active.is_(True), Slot.booked < Slot.capacity)
                         .values(booked=Slot.booked + 1))
        if got.rowcount != 1:  # lost a race for the last place
            raise ValidationError("That slot just filled up. Please pick another.")
        if quote.coupon_code:
            got = db.execute(update(Coupon).where(Coupon.code == quote.coupon_code, or_(
                Coupon.usage_limit.is_(None), Coupon.used_count < Coupon.usage_limit))
                .values(used_count=Coupon.used_count + 1))
            if got.rowcount != 1:
                raise ValidationError("That coupon has just been fully redeemed.")
        order = Order(
            order_no=_new_order_no(db), user_id=user_id, subtotal=quote.subtotal, discount=quote.discount,
            collection_fee=quote.collection_fee, total=quote.total, coupon_code=quote.coupon_code,
            payment_method=payment_method, payment_status="cod" if payment_method == "cod" else "pending",
            idempotency_key=idempotency_key, slot_id=slot_id, addr_label=addr.label,
            addr_line=", ".join(p for p in (addr.line1, addr.landmark) if p), addr_pincode=addr.pincode,
            city=quote.city or "")
        order.items = [OrderItem(patient_id=l.patient_id, item_type=l.item_type, code=l.code, name=l.name,
                                 price=l.price, mrp=l.mrp) for l in quote.lines]
        _event(db, order, "booked", "Order placed", user_id)
        db.add(order)
        audit(db, "order_created", actor_id=user_id, entity="order", entity_id=order.order_no)
        db.commit()
    except Exception:
        db.rollback()
        raise
    return _order_dto(order, False)


def _load_order(db: Session, order_no: str) -> Order:
    o = db.scalar(select(Order).where(Order.order_no == order_no))
    if o is None:
        raise ServiceError("Order not found.")
    return o


def get_order(db: Session, user_id: int, order_no: str) -> OrderDTO:
    o = _load_order(db, order_no)
    if o.user_id != user_id:
        raise ServiceError("Order not found.")  # same message: don't reveal that it exists
    return _order_dto(o, _has_report(db, o.id))


def list_orders(db: Session, user_id: int) -> list[OrderDTO]:
    rows = db.scalars(select(Order).where(Order.user_id == user_id).order_by(Order.id.desc()))
    return [_order_dto(o, _has_report(db, o.id)) for o in rows]


def _cancel(db: Session, order: Order, reason: str, actor_id: int | None) -> None:
    """Shared cancel: frees the slot and coupon, settles payment. Caller commits."""
    db.execute(update(Slot).where(Slot.id == order.slot_id, Slot.booked > 0).values(booked=Slot.booked - 1))
    if order.coupon_code:
        db.execute(update(Coupon).where(Coupon.code == order.coupon_code, Coupon.used_count > 0)
                   .values(used_count=Coupon.used_count - 1))
    order.payment_status = "refunded" if order.payment_status == "paid" else "void"  # real refunds: gateway API later
    order.status = "cancelled"
    order.cancel_reason = reason[:200]
    _event(db, order, "cancelled", reason[:200], actor_id)


def cancel_order(db: Session, user_id: int, order_no: str, reason: str, *, settings: Settings | None = None) -> OrderDTO:
    s = settings or get_settings()
    o = _load_order(db, order_no)
    if o.user_id != user_id:
        raise ServiceError("Order not found.")
    if o.status not in CUSTOMER_CANCELLABLE:
        raise ServiceError("This order can no longer be cancelled online. Contact support.")
    if o.slot.start_dt < local_now() + timedelta(hours=s.booking_cutoff_hours):
        raise ServiceError(f"Orders can be cancelled up to {s.booking_cutoff_hours} hours before the slot. "
                           "Contact support.")
    _cancel(db, o, validate_text(reason or "Cancelled by customer", "Reason", max_len=200), user_id)
    audit(db, "order_cancelled", actor_id=user_id, entity="order", entity_id=order_no)
    db.commit()
    return _order_dto(o, False)


def reschedule_order(db: Session, user_id: int, order_no: str, new_slot_id: int, *,
                     settings: Settings | None = None) -> OrderDTO:
    s = settings or get_settings()
    o = _load_order(db, order_no)
    if o.user_id != user_id:
        raise ServiceError("Order not found.")
    if o.status not in CUSTOMER_CANCELLABLE:
        raise ServiceError("This order can no longer be rescheduled online. Contact support.")
    if o.slot.start_dt < local_now() + timedelta(hours=s.booking_cutoff_hours):
        raise ServiceError(f"Orders can be rescheduled up to {s.booking_cutoff_hours} hours before the slot.")
    new = db.get(Slot, new_slot_id)
    if new is None or new.id == o.slot_id or new.city != o.city or not _slot_open(new, s):
        raise ValidationError("That time slot isn't available. Please pick another.")
    try:
        got = db.execute(update(Slot).where(Slot.id == new.id, Slot.active.is_(True), Slot.booked < Slot.capacity)
                         .values(booked=Slot.booked + 1))
        if got.rowcount != 1:
            raise ValidationError("That slot just filled up. Please pick another.")
        db.execute(update(Slot).where(Slot.id == o.slot_id, Slot.booked > 0).values(booked=Slot.booked - 1))
        old_label = f"{o.slot.day:%d %b} {o.slot.start}"
        o.slot_id = new.id
        o.slot = new
        o.phlebotomist_id = None  # the collector was assigned for the old slot
        o.status = "booked"
        _event(db, o, "booked", f"Rescheduled from {old_label} to {new.day:%d %b} {new.start}", user_id)
        audit(db, "order_rescheduled", actor_id=user_id, entity="order", entity_id=order_no)
        db.commit()
    except Exception:
        db.rollback()
        raise
    return _order_dto(o, _has_report(db, o.id))


def mock_pay(db: Session, user_id: int, order_no: str, *, settings: Settings | None = None) -> OrderDTO:
    """DEMO gateway: marks an online order paid. Disabled in production: replace with Razorpay
    (create gateway order server-side, verify the signature, confirm via webhook)."""
    s = settings or get_settings()
    if s.app_env == "production":
        raise ServiceError("Online payment isn't configured.")
    o = _load_order(db, order_no)
    if o.user_id != user_id:
        raise ServiceError("Order not found.")
    if o.status == "cancelled" or o.payment_method != "online" or o.payment_status != "pending":
        raise ServiceError("This order doesn't need a payment.")
    o.payment_status = "paid"
    o.payment_ref = "DEMO-" + secrets.token_hex(5).upper()
    _event(db, o, o.status, f"Payment received (demo) {o.payment_ref}", user_id)
    audit(db, "order_paid_demo", actor_id=user_id, entity="order", entity_id=order_no)
    db.commit()
    return _order_dto(o, _has_report(db, o.id))


def expire_unpaid_orders(db: Session, *, settings: Settings | None = None) -> int:
    """Releases slots held by online orders that weren't paid in time. Cheap; called from several pages."""
    s = settings or get_settings()
    cutoff = utcnow() - timedelta(minutes=s.payment_hold_minutes)
    stale = db.scalars(select(Order).where(Order.payment_method == "online", Order.payment_status == "pending",
                                           Order.status.in_(("booked", "assigned")), Order.created_at < cutoff)).all()
    for o in stale:
        _cancel(db, o, "Payment not completed in time", None)
        audit(db, "order_expired", entity="order", entity_id=o.order_no)
    if stale:
        db.commit()
    return len(stale)


def get_report(db: Session, user_id: int, order_no: str) -> tuple[str, bytes]:
    o = _load_order(db, order_no)
    if o.user_id != user_id:
        raise ServiceError("Order not found.")
    rep = db.scalar(select(Report).where(Report.order_id == o.id).order_by(Report.id.desc()).limit(1))
    if rep is None or o.status != "report_ready":
        raise ServiceError("Your report isn't ready yet.")
    audit(db, "report_downloaded", actor_id=user_id, entity="order", entity_id=order_no)
    db.commit()
    return rep.filename, rep.content


# ---- Admin services ------------------------------------------------------------------
# Every function re-checks the caller's role in the DATABASE (not just the UI) and writes an audit row.

def require_admin(db: Session, actor: CurrentUser) -> User:
    u = db.get(User, actor.user_id) if actor else None
    if u is None or not u.is_active or u.role != "admin":
        raise ServiceError("You don't have permission to do that.")
    return u


def _fmt_dt(dt: datetime | None) -> str:
    return dt.strftime("%d %b %Y %H:%M") if dt else ""


def _order_row(o: Order) -> dict:
    return {
        "Order": o.order_no, "Status": STATUS_LABELS[o.status], "Customer": o.user.name or "",
        "Phone": o.user.phone, "City": o.city, "Slot": f"{o.slot.day:%d %b} {o.slot.start}-{o.slot.end}",
        "Collector": o.phlebotomist.name if o.phlebotomist else "", "Total (₹)": o.total,
        "Payment": o.payment_status, "Placed": _fmt_dt(o.created_at + IST),
    }


def admin_list_orders(db: Session, actor: CurrentUser, *, status: str | None = None, city: str | None = None,
                      day_from: date | None = None, day_to: date | None = None, q: str = "",
                      limit: int = 500) -> list[dict]:
    require_admin(db, actor)
    stmt = select(Order).join(Slot, Order.slot_id == Slot.id).join(User, Order.user_id == User.id)
    if status:
        stmt = stmt.where(Order.status == status)
    if city:
        stmt = stmt.where(Order.city == city)
    if day_from:
        stmt = stmt.where(Slot.day >= day_from)
    if day_to:
        stmt = stmt.where(Slot.day <= day_to)
    q = (q or "").strip()
    if q:
        like = f"%{q}%"
        stmt = stmt.where(or_(Order.order_no.ilike(like), User.phone.ilike(like), User.name.ilike(like)))
    rows = db.scalars(stmt.order_by(Order.id.desc()).limit(limit)).all()
    return [_order_row(o) for o in rows]


def admin_get_order(db: Session, actor: CurrentUser, order_no: str) -> OrderDTO:
    require_admin(db, actor)
    o = _load_order(db, order_no)
    return _order_dto(o, _has_report(db, o.id))


def admin_assign(db: Session, actor: CurrentUser, order_no: str, phlebotomist_id: int) -> OrderDTO:
    require_admin(db, actor)
    o = _load_order(db, order_no)
    if o.status not in ("booked", "assigned"):
        raise ServiceError("A collector can only be assigned before the sample is collected.")
    ph = db.get(Phlebotomist, phlebotomist_id)
    if ph is None or not ph.active:
        raise ServiceError("Choose an active collector.")
    if ph.city != o.city:
        raise ServiceError(f"{ph.name} works in {ph.city}, but this order is in {o.city}.")
    o.phlebotomist_id = ph.id
    o.phlebotomist = ph
    o.status = "assigned"
    _event(db, o, "assigned", f"Assigned to {ph.name}", actor.user_id)
    audit(db, "order_assigned", actor_id=actor.user_id, entity="order", entity_id=order_no)
    db.commit()
    return _order_dto(o, _has_report(db, o.id))


def admin_advance(db: Session, actor: CurrentUser, order_no: str, new_status: str, note: str = "") -> OrderDTO:
    """Move an order along the allowed path. Cancelling and assigning have their own functions."""
    require_admin(db, actor)
    o = _load_order(db, order_no)
    if new_status not in TRANSITIONS.get(o.status, set()) or new_status in ("cancelled", "assigned"):
        raise ServiceError(f"An order that is '{STATUS_LABELS[o.status]}' can't move to '{STATUS_LABELS.get(new_status, new_status)}'.")
    if new_status == "report_ready" and not _has_report(db, o.id):
        raise ServiceError("Upload the report PDF first. The order becomes 'Report ready' automatically.")
    if new_status == "collected" and o.phlebotomist_id is None:
        raise ServiceError("Assign a collector first.")
    o.status = new_status
    _event(db, o, new_status, validate_text(note, "Note", min_len=0, max_len=300) or None, actor.user_id)
    audit(db, f"order_{new_status}", actor_id=actor.user_id, entity="order", entity_id=order_no)
    db.commit()
    return _order_dto(o, _has_report(db, o.id))


def admin_cancel(db: Session, actor: CurrentUser, order_no: str, reason: str) -> OrderDTO:
    require_admin(db, actor)
    o = _load_order(db, order_no)
    if "cancelled" not in TRANSITIONS.get(o.status, set()):
        raise ServiceError(f"A '{STATUS_LABELS[o.status]}' order can't be cancelled.")
    _cancel(db, o, validate_text(reason, "Reason", min_len=3, max_len=200), actor.user_id)
    audit(db, "order_cancelled_by_admin", actor_id=actor.user_id, entity="order", entity_id=order_no)
    db.commit()
    return _order_dto(o, _has_report(db, o.id))


def admin_mark_paid(db: Session, actor: CurrentUser, order_no: str, reference: str = "") -> OrderDTO:
    """For pay-on-collection orders (cash/UPI taken by the collector) or a manually verified online payment."""
    require_admin(db, actor)
    o = _load_order(db, order_no)
    if o.status == "cancelled" or o.payment_status not in ("cod", "pending"):
        raise ServiceError("This order has no payment outstanding.")
    o.payment_status = "paid"
    o.payment_ref = validate_text(reference, "Reference", min_len=0, max_len=40) or "RECEIVED"
    _event(db, o, o.status, f"Payment marked received ({o.payment_ref})", actor.user_id)
    audit(db, "order_marked_paid", actor_id=actor.user_id, entity="order", entity_id=order_no)
    db.commit()
    return _order_dto(o, _has_report(db, o.id))


def admin_add_note(db: Session, actor: CurrentUser, order_no: str, note: str) -> OrderDTO:
    require_admin(db, actor)
    o = _load_order(db, order_no)
    _event(db, o, o.status, "Note: " + validate_text(note, "Note", max_len=280), actor.user_id)
    db.commit()
    return _order_dto(o, _has_report(db, o.id))


def admin_upload_report(db: Session, actor: CurrentUser, order_no: str, filename: str, data: bytes, *,
                        settings: Settings | None = None) -> OrderDTO:
    s = settings or get_settings()
    require_admin(db, actor)
    o = _load_order(db, order_no)
    if o.status not in ("in_lab", "report_ready"):
        raise ServiceError("Mark the sample as 'At the lab' before uploading its report.")
    if not data or not data.startswith(b"%PDF-"):
        raise ValidationError("The report must be a PDF file.")
    if len(data) > s.max_report_mb * 1024 * 1024:
        raise ValidationError(f"The report is larger than {s.max_report_mb} MB.")
    safe = re.sub(r"[^A-Za-z0-9._-]", "_", filename or "report.pdf")[:100] or "report.pdf"
    db.add(Report(order_id=o.id, filename=safe if safe.lower().endswith(".pdf") else safe + ".pdf", content=data,
                  uploaded_by=actor.user_id))
    db.flush()
    if o.status == "in_lab":
        o.status = "report_ready"
        _event(db, o, "report_ready", "Report uploaded", actor.user_id)
    else:
        _event(db, o, "report_ready", "Report replaced with a newer version", actor.user_id)
    audit(db, "report_uploaded", actor_id=actor.user_id, entity="order", entity_id=order_no)
    db.commit()
    return _order_dto(o, True)


def admin_dashboard(db: Session, actor: CurrentUser) -> dict:
    require_admin(db, actor)
    now = local_now()
    today = now.date()
    status_counts = dict(db.execute(select(Order.status, func.count()).group_by(Order.status)).all())
    today_collections = db.scalar(select(func.count()).select_from(Order).join(Slot, Order.slot_id == Slot.id)
                                  .where(Slot.day == today, Order.status != "cancelled")) or 0
    pending_payments = db.scalar(select(func.count()).select_from(Order).where(
        Order.payment_status == "pending", Order.status != "cancelled")) or 0
    since = utcnow() - timedelta(days=30)
    recent = db.scalars(select(Order).options(selectinload(Order.items)).where(Order.created_at >= since)).all()
    live = [o for o in recent if o.status != "cancelled"]
    paid = [o for o in live if o.payment_status == "paid"]
    days = [today - timedelta(days=i) for i in range(13, -1, -1)]
    bookings = Counter((o.created_at + IST).date() for o in live)
    revenue = Counter()
    for o in paid:
        revenue[(o.created_at + IST).date()] += o.total
    top = Counter()
    for o in live:
        for i in o.items:
            top[i.name] += 1
    soon = db.scalars(select(Order).join(Slot, Order.slot_id == Slot.id).where(
        Order.status == "booked", Slot.day <= today + timedelta(days=1)).order_by(Slot.day, Slot.start)).all()
    return {
        "today_collections": today_collections,
        "unassigned": status_counts.get("booked", 0),
        "awaiting_reports": status_counts.get("collected", 0) + status_counts.get("in_lab", 0),
        "pending_payments": pending_payments,
        "revenue_30d": sum(o.total for o in paid),
        "orders_30d": len(live),
        "customers": db.scalar(select(func.count()).select_from(User).where(User.role == "customer")) or 0,
        "new_customers_7d": db.scalar(select(func.count()).select_from(User).where(
            User.role == "customer", User.created_at >= utcnow() - timedelta(days=7))) or 0,
        "waitlist": db.scalar(select(func.count()).select_from(PincodeWaitlist)) or 0,
        "status_counts": {STATUS_LABELS[k]: status_counts.get(k, 0) for k in ORDER_STATUSES},
        "bookings_series": {d: bookings.get(d, 0) for d in days},
        "revenue_series": {d: revenue.get(d, 0) for d in days},
        "top_items": top.most_common(6),
        "needs_assignment": [{"Order": o.order_no, "Slot": f"{o.slot.day:%d %b} {o.slot.start}", "City": o.city,
                              "Customer": o.user.name or ""} for o in soon],
    }


def admin_runsheet(db: Session, actor: CurrentUser, day: date, city: str | None = None, *, export: bool = False) -> list[dict]:
    """The collectors' day plan. Contains phone numbers and addresses, so exports are audited."""
    require_admin(db, actor)
    stmt = select(Order).join(Slot, Order.slot_id == Slot.id).where(
        Slot.day == day, Order.status.in_(("booked", "assigned", "collected")))
    if city:
        stmt = stmt.where(Order.city == city)
    rows = []
    for o in db.scalars(stmt.order_by(Slot.start, Order.id)):
        by_person: dict[str, list[str]] = {}
        for i in o.items:
            by_person.setdefault(i.patient.name, []).append(i.name)
        rows.append({
            "Slot": f"{o.slot.start}-{o.slot.end}", "Order": o.order_no, "Status": STATUS_LABELS[o.status],
            "Collector": o.phlebotomist.name if o.phlebotomist else "UNASSIGNED", "Customer": o.user.name or "",
            "Phone": o.user.phone, "Address": f"{o.addr_line}, {o.addr_pincode}", "City": o.city,
            "Samples for": "; ".join(f"{n}: {', '.join(t)}" for n, t in by_person.items()),
            "Collect cash (₹)": o.total if o.payment_status == "cod" else 0,
        })
    if export:
        audit(db, "runsheet_exported", actor_id=actor.user_id, entity="runsheet", entity_id=f"{day}:{city or 'all'}")
        db.commit()
    return rows


def rows_to_csv(rows: list[dict]) -> str:
    if not rows:
        return ""
    buf = io.StringIO()
    writer = csv.DictWriter(buf, fieldnames=list(rows[0].keys()))
    writer.writeheader()
    for r in rows:  # neutralise spreadsheet formula injection from user-supplied text
        writer.writerow({k: ("'" + v if isinstance(v, str) and v[:1] in "=+-@" and v else v) for k, v in r.items()})
    return buf.getvalue()


# catalogue ---------------------------------------------------------------------------

def admin_list_tests(db: Session, actor: CurrentUser) -> list[Test]:
    require_admin(db, actor)
    return list(db.scalars(select(Test).order_by(Test.category, Test.name)))


def admin_save_test(db: Session, actor: CurrentUser, *, code: str, name: str, category: str, description: str,
                    sample_type: str, fasting_hours: int, tat_hours: int, price: int, mrp: int, prep_notes: str,
                    interference_notes: str, popular: bool, active: bool) -> None:
    require_admin(db, actor)
    code = validate_code(code, "Test code")
    price, mrp = validate_int(price, "Price", minimum=1), validate_int(mrp, "MRP", minimum=1)
    if mrp < price:
        raise ValidationError("MRP cannot be lower than the selling price.")
    t = db.scalar(select(Test).where(Test.code == code))
    created = t is None
    if t is None:
        t = Test(code=code, name="", category="", price=0, mrp=0)
        db.add(t)
    t.name = validate_text(name, "Name", min_len=2, max_len=120)
    t.category = validate_text(category, "Category", min_len=2, max_len=40)
    t.description = validate_text(description, "Description", min_len=0, max_len=600)
    t.sample_type = validate_text(sample_type, "Sample type", max_len=30)
    t.fasting_hours = validate_int(fasting_hours, "Fasting hours", maximum=24)
    t.tat_hours = validate_int(tat_hours, "Turnaround hours", minimum=1, maximum=240)
    t.price, t.mrp = price, mrp
    t.prep_notes = validate_text(prep_notes, "Preparation notes", min_len=0, max_len=600)
    t.interference_notes = validate_text(interference_notes, "Interference notes", min_len=0, max_len=600)
    t.popular, t.active = bool(popular), bool(active)
    audit(db, "test_created" if created else "test_updated", actor_id=actor.user_id, entity="test", entity_id=code)
    db.commit()


def admin_list_packages(db: Session, actor: CurrentUser) -> list[Package]:
    require_admin(db, actor)
    return list(db.scalars(select(Package).options(selectinload(Package.tests)).order_by(Package.name)))


def admin_save_package(db: Session, actor: CurrentUser, *, code: str, name: str, description: str, audience: str,
                       price: int, mrp: int, popular: bool, active: bool, test_codes: list[str]) -> None:
    require_admin(db, actor)
    code = validate_code(code, "Panel code")
    if audience not in ("all", "male", "female"):
        raise ValidationError("Audience must be everyone, male or female.")
    price, mrp = validate_int(price, "Price", minimum=1), validate_int(mrp, "MRP", minimum=1)
    if mrp < price:
        raise ValidationError("MRP cannot be lower than the selling price.")
    tests = list(db.scalars(select(Test).where(Test.code.in_(test_codes)))) if test_codes else []
    if len(tests) < 2 or len(tests) != len(set(test_codes)):
        raise ValidationError("A panel needs at least two different, existing tests.")
    p = db.scalar(select(Package).where(Package.code == code))
    created = p is None
    if p is None:
        p = Package(code=code, name="", price=0, mrp=0)
        db.add(p)
    p.name = validate_text(name, "Name", min_len=2, max_len=120)
    p.description = validate_text(description, "Description", min_len=0, max_len=600)
    p.audience, p.price, p.mrp, p.popular, p.active = audience, price, mrp, bool(popular), bool(active)
    p.tests = tests
    audit(db, "package_created" if created else "package_updated", actor_id=actor.user_id, entity="package", entity_id=code)
    db.commit()


# locations ---------------------------------------------------------------------------

def admin_list_pincodes(db: Session, actor: CurrentUser, q: str = "") -> list[dict]:
    require_admin(db, actor)
    stmt = select(ServiceablePincode)
    q = (q or "").strip()
    if q:
        like = f"%{q}%"
        stmt = stmt.where(or_(ServiceablePincode.pincode.like(like), ServiceablePincode.city.ilike(like),
                              ServiceablePincode.area.ilike(like)))
    return [{"Pincode": r.pincode, "Area": r.area or "", "City": r.city, "State": r.state,
             "Status": "Serviceable" if r.active else "Coming soon", "Fee (₹)": r.collection_fee}
            for r in db.scalars(stmt.order_by(ServiceablePincode.pincode).limit(500))]


def admin_save_pincode(db: Session, actor: CurrentUser, *, pincode: str, area: str | None, city: str, state: str,
                       active: bool, fee: int) -> None:
    require_admin(db, actor)
    pin = validate_pincode(pincode)
    row = db.get(ServiceablePincode, pin) or ServiceablePincode(pincode=pin, city="", state="")
    row.area = validate_text(area, "Area", min_len=0, max_len=80) or None if area else None
    row.city = validate_text(city, "City", min_len=2, max_len=80)
    row.state = validate_text(state, "State", min_len=2, max_len=80)
    row.active = bool(active)
    row.collection_fee = validate_int(fee, "Collection fee", maximum=1000)
    db.add(row)
    audit(db, "pincode_saved", actor_id=actor.user_id, entity="pincode", entity_id=pin)
    db.commit()


def admin_import_pincodes(db: Session, actor: CurrentUser, text: str) -> tuple[int, list[str]]:
    """CSV with header: pincode,area,city,state,active,collection_fee. Valid rows are saved; bad rows are reported."""
    require_admin(db, actor)
    reader = csv.DictReader(io.StringIO(text.lstrip("\ufeff")))
    needed = {"pincode", "city", "state"}
    if not reader.fieldnames or not needed <= {f.strip().lower() for f in reader.fieldnames}:
        raise ValidationError("The CSV needs a header row with at least: pincode, city, state.")
    ok, errors = 0, []
    for n, raw in enumerate(reader, start=2):
        r = {(k or "").strip().lower(): (v or "").strip() for k, v in raw.items()}
        try:
            pin = validate_pincode(r.get("pincode", ""))
            row = db.get(ServiceablePincode, pin) or ServiceablePincode(pincode=pin, city="", state="")
            row.area = r.get("area") or None
            row.city = validate_text(r.get("city", ""), "City", min_len=2, max_len=80)
            row.state = validate_text(r.get("state", ""), "State", min_len=2, max_len=80)
            row.active = r.get("active", "1").lower() in {"1", "true", "yes", "y"}
            row.collection_fee = validate_int(r.get("collection_fee") or 0, "Collection fee", maximum=1000)
            db.add(row)
            ok += 1
        except ServiceError as exc:
            errors.append(f"Line {n}: {exc}")
    audit(db, "pincodes_imported", actor_id=actor.user_id, entity="pincode", entity_id=str(ok))
    db.commit()
    return ok, errors


def admin_waitlist(db: Session, actor: CurrentUser) -> list[dict]:
    """Demand signal: where customers are asking for service, most-requested first."""
    require_admin(db, actor)
    out = []
    for pin, total, with_phone in db.execute(
            select(PincodeWaitlist.pincode, func.count(), func.count(PincodeWaitlist.phone))
            .group_by(PincodeWaitlist.pincode).order_by(func.count().desc())):
        row = db.get(ServiceablePincode, pin)
        out.append({"Pincode": pin, "Place": (row.area or row.city) if row else "Not in directory",
                    "Status": ("Serviceable" if row.active else "Coming soon") if row else "Unknown",
                    "Requests": total, "With phone": with_phone})
    return out


def admin_clear_waitlist(db: Session, actor: CurrentUser, pincode: str) -> int:
    """After launching a pincode and notifying people, clear its waitlist."""
    require_admin(db, actor)
    pin = validate_pincode(pincode)
    n = db.query(PincodeWaitlist).filter(PincodeWaitlist.pincode == pin).delete()
    audit(db, "waitlist_cleared", actor_id=actor.user_id, entity="pincode", entity_id=pin)
    db.commit()
    return n


# slots -------------------------------------------------------------------------------

def admin_generate_slots(db: Session, actor: CurrentUser, *, city: str, start_day: date, end_day: date,
                         windows: list[tuple[str, str]], capacity: int, skip_sundays: bool = False) -> tuple[int, int]:
    """Creates missing slots only (never touches existing ones). Returns (created, already_existed)."""
    require_admin(db, actor)
    city = validate_text(city, "City", min_len=2, max_len=80)
    if end_day < start_day or (end_day - start_day).days > 60:
        raise ValidationError("Choose a date range of up to 60 days.")
    capacity = validate_int(capacity, "Capacity", minimum=1, maximum=500)
    wins = []
    for a, b in windows:
        a, b = validate_hhmm(a), validate_hhmm(b)
        if a >= b:
            raise ValidationError(f"The window {a} to {b} ends before it starts.")
        wins.append((a, b))
    if not wins:
        raise ValidationError("Add at least one time window.")
    created = existed = 0
    day = start_day
    while day <= end_day:
        if not (skip_sundays and day.weekday() == 6):
            for a, b in wins:
                if db.scalar(select(Slot.id).where(Slot.city == city, Slot.day == day, Slot.start == a)):
                    existed += 1
                else:
                    db.add(Slot(city=city, day=day, start=a, end=b, capacity=capacity))
                    created += 1
        day += timedelta(days=1)
    audit(db, "slots_generated", actor_id=actor.user_id, entity="slot", entity_id=f"{city}:{created}")
    db.commit()
    return created, existed


def admin_list_slots(db: Session, actor: CurrentUser, city: str | None, day_from: date, day_to: date) -> list[SlotDTO]:
    require_admin(db, actor)
    stmt = select(Slot).where(Slot.day >= day_from, Slot.day <= day_to)
    if city:
        stmt = stmt.where(Slot.city == city)
    return [_slot_dto(s_) for s_ in db.scalars(stmt.order_by(Slot.day, Slot.start, Slot.city))]


def admin_update_slot(db: Session, actor: CurrentUser, slot_id: int, *, capacity: int, active: bool) -> None:
    require_admin(db, actor)
    sl = db.get(Slot, slot_id)
    if sl is None:
        raise ServiceError("Slot not found.")
    capacity = validate_int(capacity, "Capacity", minimum=1, maximum=500)
    if capacity < sl.booked:
        raise ValidationError(f"{sl.booked} orders are already booked in this slot. Capacity can't go below that.")
    sl.capacity, sl.active = capacity, bool(active)  # deactivating keeps existing bookings, blocks new ones
    audit(db, "slot_updated", actor_id=actor.user_id, entity="slot", entity_id=slot_id)
    db.commit()


# collectors and coupons ---------------------------------------------------------------

def admin_list_phlebotomists(db: Session, actor: CurrentUser) -> list[dict]:
    require_admin(db, actor)
    open_orders = dict(db.execute(select(Order.phlebotomist_id, func.count()).where(
        Order.status.in_(("assigned", "collected"))).group_by(Order.phlebotomist_id)).all())
    return [{"ID": p.id, "Name": p.name, "Phone": p.phone, "City": p.city, "Active": p.active,
             "Open orders": open_orders.get(p.id, 0)} for p in db.scalars(select(Phlebotomist).order_by(Phlebotomist.city, Phlebotomist.name))]


def admin_save_phlebotomist(db: Session, actor: CurrentUser, *, phlebotomist_id: int | None, name: str, phone: str,
                            city: str, active: bool) -> None:
    require_admin(db, actor)
    p = db.get(Phlebotomist, phlebotomist_id) if phlebotomist_id else Phlebotomist(name="", phone="", city="")
    if p is None:
        raise ServiceError("Collector not found.")
    p.name = validate_name(name)
    p.phone = normalize_phone(phone)
    p.city = validate_text(city, "City", min_len=2, max_len=80)
    p.active = bool(active)
    db.add(p)
    db.flush()
    audit(db, "collector_saved", actor_id=actor.user_id, entity="phlebotomist", entity_id=p.id)
    db.commit()


def admin_list_coupons(db: Session, actor: CurrentUser) -> list[Coupon]:
    require_admin(db, actor)
    return list(db.scalars(select(Coupon).order_by(Coupon.active.desc(), Coupon.code)))


def admin_save_coupon(db: Session, actor: CurrentUser, *, code: str, kind: str, value: int, min_order: int,
                      max_discount: int | None, valid_from: date | None, valid_to: date | None,
                      usage_limit: int | None, per_user_limit: int, active: bool) -> None:
    require_admin(db, actor)
    code = validate_code(code, "Coupon code")
    if kind not in ("percent", "flat"):
        raise ValidationError("Coupon type must be percent or flat.")
    value = validate_int(value, "Value", minimum=1, maximum=100 if kind == "percent" else 100_000)
    if valid_from and valid_to and valid_to < valid_from:
        raise ValidationError("The end date is before the start date.")
    c = db.scalar(select(Coupon).where(Coupon.code == code))
    created = c is None
    if c is None:
        c = Coupon(code=code, kind=kind, value=value)
        db.add(c)
    c.kind, c.value = kind, value
    c.min_order = validate_int(min_order, "Minimum order")
    c.max_discount = validate_int(max_discount, "Maximum discount", minimum=1) if max_discount else None
    c.valid_from, c.valid_to = valid_from, valid_to
    c.usage_limit = validate_int(usage_limit, "Usage limit", minimum=1) if usage_limit else None
    c.per_user_limit = validate_int(per_user_limit, "Per-customer limit", minimum=1, maximum=100)
    c.active = bool(active)
    audit(db, "coupon_created" if created else "coupon_updated", actor_id=actor.user_id, entity="coupon", entity_id=code)
    db.commit()


# customers and audit --------------------------------------------------------------------

def admin_search_customers(db: Session, actor: CurrentUser, q: str = "", limit: int = 200) -> list[dict]:
    require_admin(db, actor)
    stmt = select(User)
    q = (q or "").strip()
    if q:
        like = f"%{q}%"
        stmt = stmt.where(or_(User.phone.ilike(like), User.name.ilike(like), User.email.ilike(like)))
    counts = dict(db.execute(select(Order.user_id, func.count()).group_by(Order.user_id)).all())
    return [{"ID": u.id, "Name": u.name or "(profile incomplete)", "Phone": mask_phone(u.phone), "Role": u.role,
             "Active": u.is_active, "Orders": counts.get(u.id, 0), "Joined": _fmt_dt(u.created_at + IST)}
            for u in db.scalars(stmt.order_by(User.id.desc()).limit(limit))]


def admin_customer_detail(db: Session, actor: CurrentUser, user_id: int) -> dict:
    """Shows full contact details, so every view is audited (DPDP accountability)."""
    require_admin(db, actor)
    u = db.get(User, user_id)
    if u is None:
        raise ServiceError("Customer not found.")
    audit(db, "customer_viewed", actor_id=actor.user_id, entity="user", entity_id=user_id)
    db.commit()
    consents = [{"Purpose": c.purpose, "Granted": c.granted, "Version": c.version, "When": _fmt_dt(c.created_at + IST)}
                for c in db.scalars(select(ConsentRecord).where(ConsentRecord.user_id == user_id))]
    return {"id": u.id, "name": u.name, "phone": u.phone, "email": u.email, "dob": u.dob, "sex": u.sex,
            "pincode": u.home_pincode, "role": u.role, "active": u.is_active, "joined": _fmt_dt(u.created_at + IST),
            "last_login": _fmt_dt(u.last_login_at + IST if u.last_login_at else None), "consents": consents,
            "orders": [_order_row(o) for o in db.scalars(select(Order).where(Order.user_id == user_id).order_by(Order.id.desc()))],
            "family": [_patient_dto(p) for p in db.scalars(select(Patient).where(Patient.user_id == user_id, Patient.active.is_(True)))]}


def admin_set_user_active(db: Session, actor: CurrentUser, user_id: int, active: bool) -> None:
    require_admin(db, actor)
    if user_id == actor.user_id:
        raise ServiceError("You can't disable your own account.")
    u = db.get(User, user_id)
    if u is None:
        raise ServiceError("Customer not found.")
    u.is_active = bool(active)
    if not active:  # sign them out everywhere, immediately
        for sess in db.scalars(select(UserSession).where(UserSession.user_id == user_id, UserSession.revoked.is_(False))):
            sess.revoked = True
    audit(db, "user_enabled" if active else "user_disabled", actor_id=actor.user_id, entity="user", entity_id=user_id)
    db.commit()


def admin_set_role(db: Session, actor: CurrentUser, user_id: int, role: str) -> None:
    require_admin(db, actor)
    if role not in ("customer", "admin"):
        raise ValidationError("Role must be customer or admin.")
    if user_id == actor.user_id:
        raise ServiceError("You can't change your own role. Ask another admin.")
    u = db.get(User, user_id)
    if u is None:
        raise ServiceError("Customer not found.")
    u.role = role
    audit(db, f"role_set_{role}", actor_id=actor.user_id, entity="user", entity_id=user_id)
    db.commit()


def admin_audit_log(db: Session, actor: CurrentUser, action: str | None = None, limit: int = 500) -> list[dict]:
    require_admin(db, actor)
    stmt = select(AuditLog)
    if action:
        stmt = stmt.where(AuditLog.action == action)
    return [{"When": _fmt_dt(a.created_at + IST), "Action": a.action, "Actor": a.actor_id if a.actor_id else "system",
             "Entity": a.entity or "", "Entity ID": a.entity_id or ""}
            for a in db.scalars(stmt.order_by(AuditLog.id.desc()).limit(limit))]


def admin_audit_actions(db: Session, actor: CurrentUser) -> list[str]:
    require_admin(db, actor)
    return list(db.scalars(select(AuditLog.action).distinct().order_by(AuditLog.action)))


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
                if st.button("Add to cart", key=f"add_package_{p.code}"):
                    add_to_cart("package", p.code, p.name)
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
                if st.button("Add to cart", key=f"add_test_{t.code}"):
                    add_to_cart("test", t.code, t.name)
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
    st.subheader("Saved addresses")
    with session_scope() as db:
        addresses = list_addresses(db, user.user_id)
        family = list_patients(db, user.user_id)
    for a in addresses:
        c1, c2 = st.columns([6, 1], vertical_alignment="center")
        c1.markdown(f"**{esc(a.label)}**: {esc(a.text)}")
        if c2.button("Remove", key=f"rm_addr_{a.id}"):
            with session_scope() as db:
                delete_address(db, user.user_id, a.id)
            st.rerun()
    with st.expander("Add an address"):
        _address_form(user, "account")
    st.subheader("People you book for")
    for p in family:
        c1, c2 = st.columns([6, 1], vertical_alignment="center")
        c1.markdown(f"**{esc(p.name)}** ({esc(p.relation)}), {esc(p.sex)}, born {p.dob:%d %b %Y}")
        if p.relation != "self" and c2.button("Remove", key=f"rm_pat_{p.id}"):
            with session_scope() as db:
                delete_patient(db, user.user_id, p.id)
            st.rerun()
    with st.expander("Add a family member"):
        _patient_form(user, "account")
    st.divider()
    if st.button("Sign out"):
        with session_scope() as db:
            logout(db, st.session_state.get("session_token"))
        st.session_state.pop("session_token", None)
        clear_auth_flow()
        st.rerun()


def render_header() -> None:
    left, mid, right = st.columns([3, 3, 2], vertical_alignment="center")
    left.markdown(f'<p class="cm-brand">{esc(BRAND)}<span>.</span></p>', unsafe_allow_html=True)
    if "cart" in PAGES:
        right.page_link(PAGES["cart"], label=f"Cart ({len(cart_lines())})", icon=":material/shopping_cart:")
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


# ---- customer: cart, checkout, orders ----------------------------------------------------

def flash(message: str, kind: str = "success") -> None:
    """Message shown on the next run (survives st.rerun)."""
    st.session_state["_flash"] = (kind, message)


def show_flash() -> None:
    item = st.session_state.pop("_flash", None)
    if item:
        getattr(st, item[0])(item[1])


def cart_lines() -> list[dict]:
    return st.session_state.setdefault("cart", [])


def add_to_cart(item_type: str, code: str, name: str) -> None:
    cart = cart_lines()
    if any(l["type"] == item_type and l["code"] == code for l in cart):
        st.toast(f"{name} is already in your cart.")
        return
    cart.append({"id": secrets.token_hex(4), "type": item_type, "code": code, "patient_id": None})
    st.toast(f"Added {name} to your cart.")


def _catalog_lookup(db: Session) -> dict[tuple[str, str], tuple[str, int, int]]:
    out = {("test", t.code): (t.name, t.price, t.mrp) for t in search_tests(db)}
    out.update({("package", p.code): (p.name, p.price, p.mrp) for p in list_packages(db)})
    return out


def _signin_prompt(message: str) -> None:
    st.info(message)
    if "login" in PAGES:
        st.page_link(PAGES["login"], label="Sign in or create an account")


def _address_form(user: CurrentUser, key: str) -> None:
    with st.form(f"addr_form_{key}", clear_on_submit=True):
        label = st.text_input("Label", value="Home", max_chars=30)
        line1 = st.text_input("Address (house, street, area)", max_chars=200)
        landmark = st.text_input("Landmark (optional)", max_chars=120)
        pincode = st.text_input("Pincode", value=user.home_pincode or "", max_chars=6)
        if st.form_submit_button("Save address"):
            try:
                with session_scope() as db:
                    add_address(db, user.user_id, label=label, line1=line1, landmark=landmark, pincode=pincode)
                flash("Address saved.")
                st.rerun()
            except ServiceError as exc:
                st.error(str(exc))


def _patient_form(user: CurrentUser, key: str) -> None:
    with st.form(f"patient_form_{key}", clear_on_submit=True):
        name = st.text_input("Full name", max_chars=120)
        dob = st.date_input("Date of birth", value=date(1990, 1, 1), min_value=date(1900, 1, 1),
                            max_value=date.today(), format="DD/MM/YYYY")
        sex = st.radio("Sex", SEX_OPTIONS, horizontal=True)
        relation = st.selectbox("Relationship to you", [r for r in RELATIONS if r != "self"])
        if st.form_submit_button("Add person"):
            try:
                with session_scope() as db:
                    add_patient(db, user.user_id, name=name, dob=dob, sex=sex, relation=relation)
                flash("Person added.")
                st.rerun()
            except ServiceError as exc:
                st.error(str(exc))


def page_cart() -> None:
    st.title("Your cart")
    if "last_order" in st.session_state:
        _order_confirmation(st.session_state["last_order"])
        return
    cart = cart_lines()
    if not cart:
        st.info("Your cart is empty.")
        if "tests" in PAGES:
            st.page_link(PAGES["tests"], label="Browse tests and panels")
        return
    user = current_user()
    with session_scope() as db:
        catalog = _catalog_lookup(db)
    if not is_authenticated(user):
        for line in cart:
            name, price, _ = catalog.get((line["type"], line["code"]), ("(unavailable)", 0, 0))
            st.markdown(f"- **{name}**: ₹{price:,}")
        _signin_prompt("Sign in to choose who each test is for and pick a collection time.")
        return

    with session_scope() as db:
        expire_unpaid_orders(db)
        patients = list_patients(db, user.user_id)
        addresses = list_addresses(db, user.user_id)
    if not patients:
        st.error("Your profile has no patient record. Please contact support.")
        return
    pid_options = [p.id for p in patients]
    pname = {p.id: f"{p.name} ({p.relation})" for p in patients}

    st.subheader("1. Who is each test for?")
    for line in list(cart):
        if (line["type"], line["code"]) not in catalog:
            cart.remove(line)  # item was deactivated by an admin
            st.warning("An item in your cart is no longer available and was removed.")
            continue
        name, price, _ = catalog[(line["type"], line["code"])]
        c1, c2, c3, c4 = st.columns([4, 3, 1, 1], vertical_alignment="center")
        c1.markdown(f"**{name}**  \n₹{price:,}")
        current = line["patient_id"] if line["patient_id"] in pid_options else pid_options[0]
        line["patient_id"] = c2.selectbox("For", pid_options, index=pid_options.index(current), format_func=pname.get,
                                          key=f"cart_pt_{line['id']}", label_visibility="collapsed")
        if c3.button("Copy", key=f"cart_cp_{line['id']}", help="Add the same item for another person"):
            cart.append({**line, "id": secrets.token_hex(4), "patient_id": None})
            st.rerun()
        if c4.button("Remove", key=f"cart_rm_{line['id']}"):
            cart.remove(line)
            st.rerun()
    with st.expander("Add a family member"):
        _patient_form(user, "cart")

    st.subheader("2. Collection address")
    if not addresses:
        st.write("Add the address where the sample should be collected.")
        _address_form(user, "cart")
        return
    addr_id = st.radio("Address", [a.id for a in addresses], key="checkout_address",
                       format_func=lambda i: next(f"{a.label}: {a.text}" for a in addresses if a.id == i))
    chosen = next(a for a in addresses if a.id == addr_id)
    with st.expander("Add another address"):
        _address_form(user, "cart2")
    with session_scope() as db:
        coverage = check_pincode(db, chosen.pincode)
    if not coverage.serviceable:
        st.error(f"We can't collect samples at {chosen.pincode} yet. Choose another address.")
        return

    st.subheader("3. Date and time")
    with session_scope() as db:
        slots = bookable_slots(db, coverage.city)
    if not slots:
        st.warning("No collection slots are open right now. Please check back soon.")
        return
    days = sorted({s_.day for s_ in slots})
    day = st.selectbox("Date", days, format_func=lambda d: d.strftime("%A, %d %B"), key="checkout_day")
    todays = [s_ for s_ in slots if s_.day == day]
    slot_id = st.radio("Time window", [s_.id for s_ in todays], horizontal=True, key="checkout_slot",
                       format_func=lambda i: next(f"{s_.label} ({s_.remaining} left)" for s_ in todays if s_.id == i))

    st.subheader("4. Coupon")
    c1, c2, c3 = st.columns([3, 1, 1], vertical_alignment="bottom")
    code_in = c1.text_input("Coupon code", key="coupon_input", max_chars=30)
    if c2.button("Apply") and code_in.strip():
        st.session_state["coupon_code"] = code_in.strip().upper()
    if c3.button("Remove coupon"):
        st.session_state.pop("coupon_code", None)
        st.rerun()

    items = [{"type": l["type"], "code": l["code"], "patient_id": l["patient_id"]} for l in cart]
    quote = None
    coupon = st.session_state.get("coupon_code")
    try:
        with session_scope() as db:
            try:
                quote = build_quote(db, user.user_id, items, pincode=chosen.pincode, coupon_code=coupon)
            except ValidationError as exc:
                if not coupon:
                    raise
                st.session_state.pop("coupon_code", None)
                st.warning(str(exc))
                quote = build_quote(db, user.user_id, items, pincode=chosen.pincode)
    except ServiceError as exc:
        st.error(str(exc))
        return

    st.subheader("5. Review and pay")
    with st.container(border=True):
        for l in quote.lines:
            st.markdown(f"{l.name} for **{l.patient_name}**: ₹{l.price:,}")
        st.markdown(f"Subtotal: ₹{quote.subtotal:,}")
        if quote.discount:
            st.markdown(f"Coupon {quote.coupon_code}: −₹{quote.discount:,}")
        st.markdown("Home collection: " + (f"₹{quote.collection_fee:,}" if quote.collection_fee else "Free"))
        st.markdown(f"### Total: ₹{quote.total:,}")
    methods = {"Pay on collection (cash or UPI to the collector)": "cod"}
    if get_settings().app_env != "production":
        methods = {"Pay online (demo gateway)": "online", **methods}
    method = methods[st.radio("Payment", list(methods), key="checkout_payment")]
    ack = st.checkbox("I understand tumour markers are not stand-alone screening tests and that results "
                      "should be discussed with a doctor.", key="checkout_ack")
    if st.button("Confirm booking", type="primary"):
        if not ack:
            st.error("Please tick the box above to continue.")
            return
        key = st.session_state.setdefault("checkout_key", secrets.token_hex(16))
        try:
            with session_scope() as db:
                order = create_order(db, user.user_id, items=items, address_id=addr_id, slot_id=slot_id,
                                     payment_method=method, coupon_code=quote.coupon_code, idempotency_key=key)
        except ServiceError as exc:
            st.error(str(exc))
            return
        for k in ("coupon_code", "checkout_key", "checkout_ack"):
            st.session_state.pop(k, None)
        st.session_state["cart"] = []
        st.session_state["last_order"] = order.order_no
        st.rerun()


def _preparation(db: Session, order: OrderDTO) -> list[tuple[str, str]]:
    codes: dict[str, None] = {}
    for it in order.items:
        if it.item_type == "test":
            codes[it.code] = None
        else:
            pkg = db.scalar(select(Package).options(selectinload(Package.tests)).where(Package.code == it.code))
            for t in (pkg.tests if pkg else []):
                codes[t.code] = None
    tests = db.scalars(select(Test).where(Test.code.in_(list(codes)))).all()
    return [(t.name, t.prep_notes) for t in tests if t.prep_notes]


def _pay_button(user: CurrentUser, order: OrderDTO, key: str) -> None:
    if order.payment_method == "online" and order.payment_status == "pending" and order.status != "cancelled" \
            and get_settings().app_env != "production":
        st.warning(f"Payment pending. Your slot is held for {get_settings().payment_hold_minutes} minutes.")
        if st.button(f"Pay ₹{order.total:,} now (demo gateway)", key=f"pay_{key}_{order.order_no}", type="primary"):
            try:
                with session_scope() as db:
                    mock_pay(db, user.user_id, order.order_no)
                flash("Payment received (demo).")
                st.rerun()
            except ServiceError as exc:
                st.error(str(exc))


def _order_confirmation(order_no: str) -> None:
    user = current_user()
    if not is_authenticated(user):
        st.session_state.pop("last_order", None)
        st.rerun()
    try:
        with session_scope() as db:
            order = get_order(db, user.user_id, order_no)
            prep = _preparation(db, order)
    except ServiceError as exc:
        st.session_state.pop("last_order", None)
        st.error(str(exc))
        return
    st.success(f"Booking confirmed. Your order number is **{order.order_no}**.")
    st.markdown(f"**Collection:** {order.slot.day:%A, %d %B}, {order.slot.label}  \n**Address:** {order.address_text}, "
                f"{order.address_pincode}  \n**Total:** ₹{order.total:,} ({'pay on collection' if order.payment_method == 'cod' else 'online'})")
    _pay_button(user, order, "confirm")
    if prep:
        with st.expander("How to prepare for your sample", expanded=True):
            for name, note in prep:
                st.markdown(f"**{name}.** {note}")
    c1, c2 = st.columns(2)
    if "orders" in PAGES:
        c1.page_link(PAGES["orders"], label="View my orders")
    if c2.button("Book another test"):
        st.session_state.pop("last_order", None)
        st.rerun()


def _order_card(user: CurrentUser, o: OrderDTO) -> None:
    chips([(o.status_label, "green" if o.status == "report_ready" else ("" if o.status != "cancelled" else "gold")),
           (f"Payment: {o.payment_status}", "")])
    st.markdown(f"**Collection:** {o.slot.day:%A, %d %B}, {o.slot.label}  \n**Address:** {o.address_text}, {o.address_pincode}")
    if o.phlebotomist_name:
        st.markdown(f"**Collector:** {o.phlebotomist_name}")
    for it in o.items:
        st.markdown(f"- {it.name} for **{it.patient_name}**: ₹{it.price:,}")
    st.markdown(f"Total: **₹{o.total:,}**" + (f" (coupon {o.coupon_code}: −₹{o.discount:,})" if o.discount else ""))
    if o.cancel_reason:
        st.caption(f"Cancelled: {o.cancel_reason}")
    with st.expander("Timeline"):
        for e in o.events:
            st.markdown(f"- {e.created_at:%d %b %H:%M}: {STATUS_LABELS.get(e.status, e.status)}" + (f" ({e.note})" if e.note else ""))
    _pay_button(user, o, "orders")

    if o.status == "report_ready" and o.has_report:
        rkey = f"report_{o.order_no}"
        if rkey in st.session_state:
            fname, data = st.session_state[rkey]
            st.download_button("Download report (PDF)", data=data, file_name=fname, mime="application/pdf", key=f"dl_{o.order_no}")
        elif st.button("Get my report", key=f"getrep_{o.order_no}", type="primary"):
            try:
                with session_scope() as db:
                    st.session_state[rkey] = get_report(db, user.user_id, o.order_no)
                st.rerun()
            except ServiceError as exc:
                st.error(str(exc))
        st.caption("Please discuss your results with your doctor.")

    s = get_settings()
    if o.status in CUSTOMER_CANCELLABLE and \
            datetime.combine(o.slot.day, time.fromisoformat(o.slot.start)) >= local_now() + timedelta(hours=s.booking_cutoff_hours):
        with st.expander("Change time or cancel"):
            with session_scope() as db:
                options = [x for x in bookable_slots(db, o.city) if x.id != o.slot.id]
            if options:
                new_id = st.selectbox("New time", [x.id for x in options], key=f"rs_{o.order_no}",
                                      format_func=lambda i: next(f"{x.day:%a %d %b}, {x.label} ({x.remaining} left)" for x in options if x.id == i))
                if st.button("Reschedule", key=f"rsb_{o.order_no}"):
                    try:
                        with session_scope() as db:
                            reschedule_order(db, user.user_id, o.order_no, new_id)
                        flash("Your order has been rescheduled.")
                        st.rerun()
                    except ServiceError as exc:
                        st.error(str(exc))
            reason = st.text_input("Reason for cancelling", key=f"cr_{o.order_no}", max_chars=200)
            if st.button("Cancel this order", key=f"cb_{o.order_no}"):
                try:
                    with session_scope() as db:
                        cancel_order(db, user.user_id, o.order_no, reason or "Cancelled by customer")
                    flash("Order cancelled." + (" Any payment will be refunded." if o.payment_status == "paid" else ""), "info")
                    st.rerun()
                except ServiceError as exc:
                    st.error(str(exc))


def page_orders() -> None:
    st.title("My orders")
    user = current_user()
    if not is_authenticated(user):
        _signin_prompt("Sign in to see your orders.")
        return
    with session_scope() as db:
        expire_unpaid_orders(db)
        orders = list_orders(db, user.user_id)
    if not orders:
        st.info("You haven't booked anything yet.")
        if "tests" in PAGES:
            st.page_link(PAGES["tests"], label="Browse tests and panels")
        return
    for i, o in enumerate(orders):
        with st.expander(f"{o.order_no}  |  {o.status_label}  |  ₹{o.total:,}", expanded=(i == 0)):
            _order_card(user, o)


# ---- admin pages ---------------------------------------------------------------------------
# Each page checks the role again (_admin) AND every service call re-checks it in the database.

def _admin() -> CurrentUser | None:
    user = current_user()
    if user is None or user.role != "admin" or not user.profile_complete:
        st.error("This area is for administrators only.")
        return None
    return user


def _table(rows: list[dict], empty: str = "Nothing to show.") -> None:
    if rows:
        st.dataframe(rows, hide_index=True)
    else:
        st.caption(empty)


def _export(label: str, key: str, make_csv, filename: str) -> None:
    """Two-step export so the download (and its audit row) happens on click, not on every rerun."""
    if st.button(label, key=f"{key}_prep"):
        st.session_state[f"{key}_csv"] = make_csv()
    if f"{key}_csv" in st.session_state:
        st.download_button("Download CSV", st.session_state[f"{key}_csv"], file_name=filename, mime="text/csv",
                           key=f"{key}_dl")


def _cities(db: Session) -> list[str]:
    return [c for (c,) in db.execute(select(ServiceablePincode.city).distinct().order_by(ServiceablePincode.city))]


def _series_df(series: dict, name: str):
    import pandas as pd  # installed with Streamlit
    return pd.DataFrame({name: list(series.values())}, index=pd.to_datetime(list(series.keys())))


def page_admin_overview() -> None:
    admin = _admin()
    if not admin:
        return
    st.title("Admin overview")
    with session_scope() as db:
        expire_unpaid_orders(db)
        d = admin_dashboard(db, admin)
    c1, c2, c3, c4 = st.columns(4)
    c1.metric("Collections today", d["today_collections"])
    c2.metric("Awaiting a collector", d["unassigned"])
    c3.metric("Awaiting reports", d["awaiting_reports"])
    c4.metric("Payments pending", d["pending_payments"])
    c5, c6, c7, c8 = st.columns(4)
    c5.metric("Revenue, 30 days", f"₹{d['revenue_30d']:,}", help="Paid, non-cancelled orders")
    c6.metric("Orders, 30 days", d["orders_30d"])
    c7.metric("Customers", d["customers"], delta=f"+{d['new_customers_7d']} this week")
    c8.metric("Waitlist requests", d["waitlist"], help="People asking for pincodes you don't serve yet")

    st.subheader("Needs a collector (today and tomorrow)")
    _table(d["needs_assignment"], "Every order due in the next two days has a collector.")
    a, b = st.columns(2)
    with a:
        st.subheader("Orders placed, last 14 days")
        st.bar_chart(_series_df(d["bookings_series"], "Orders"))
    with b:
        st.subheader("Revenue, last 14 days (₹)")
        st.bar_chart(_series_df(d["revenue_series"], "Revenue"))
    a, b = st.columns(2)
    with a:
        st.subheader("Orders by status")
        _table([{"Status": k, "Orders": v} for k, v in d["status_counts"].items()])
    with b:
        st.subheader("Most ordered, 30 days")
        _table([{"Test or panel": k, "Orders": v} for k, v in d["top_items"]], "No orders yet.")
    with st.expander("System status"):
        s = get_settings()
        st.markdown(
            f"- Environment: **{s.app_env}**\n- Database: **{s.database_url.split(':', 1)[0]}**\n"
            f"- SMS provider: **{s.sms_provider}** (OTP shown on screen: **{'yes' if s.show_dev_otp else 'no'}**)\n"
            f"- Online payment: **{'demo gateway' if s.app_env != 'production' else 'not configured: pay on collection only'}**\n"
            f"- Admin numbers configured: **{len(s.admin_phones)}**\n"
            f"- Booking cut-off: **{s.booking_cutoff_hours} h**, window: **{s.booking_window_days} days**, payment hold: **{s.payment_hold_minutes} min**\n"
            f"- Free collection from: **₹{s.free_collection_threshold:,}**")


def _admin_order_panel(admin: CurrentUser, order_no: str) -> None:
    with session_scope() as db:
        o = admin_get_order(db, admin, order_no)
        collectors = [p for p in admin_list_phlebotomists(db, admin) if p["City"] == o.city and p["Active"]]
    st.subheader(f"{o.order_no}: {o.status_label}")
    left, right = st.columns(2)
    left.markdown(f"**Customer:** {esc(o.customer_name or '')}  \n**Phone:** {o.customer_phone}  \n"
                  f"**Address:** {esc(o.address_text)}, {o.address_pincode} ({esc(o.city)})  \n"
                  f"**Slot:** {o.slot.day:%a %d %b}, {o.slot.label}  \n**Collector:** {esc(o.phlebotomist_name or 'not assigned')}")
    right.markdown(f"**Payment:** {o.payment_method} / {o.payment_status}" + (f" ({esc(o.payment_ref)})" if o.payment_ref else "")
                   + f"  \n**Subtotal:** ₹{o.subtotal:,}  \n**Discount:** ₹{o.discount:,}" + (f" ({o.coupon_code})" if o.coupon_code else "")
                   + f"  \n**Collection fee:** ₹{o.collection_fee:,}  \n**Total:** ₹{o.total:,}")
    _table([{"For": i.patient_name, "Item": i.name, "Price (₹)": i.price} for i in o.items])
    with st.expander("Timeline", expanded=False):
        for e in o.events:
            who = "system" if e.actor_id is None else f"user {e.actor_id}"
            st.markdown(f"- {e.created_at:%d %b %H:%M}: **{STATUS_LABELS.get(e.status, e.status)}**" + (f" ({esc(e.note)})" if e.note else "") + f" by {who}")

    st.markdown("#### Actions")
    k = o.order_no

    def run(action, success: str) -> None:
        try:
            with session_scope() as db:
                action(db)
            flash(success)
            st.rerun()
        except ServiceError as exc:
            st.error(str(exc))

    if o.status in ("booked", "assigned"):
        if collectors:
            pid = st.selectbox("Collector", [c["ID"] for c in collectors], key=f"as_{k}",
                               format_func=lambda i: next(f"{c['Name']} ({c['Open orders']} open)" for c in collectors if c["ID"] == i))
            if st.button("Assign collector" if o.status == "booked" else "Reassign collector", key=f"asb_{k}"):
                run(lambda db: admin_assign(db, admin, k, pid), "Collector assigned.")
        else:
            st.warning(f"No active collectors in {o.city}. Add one under Admin > Collectors.")
    nxt = {"assigned": ("collected", "Mark sample collected"), "collected": ("in_lab", "Mark received at lab")}.get(o.status)
    if nxt:
        note = st.text_input("Note (optional)", key=f"nt_{k}", max_chars=300)
        if st.button(nxt[1], key=f"adv_{k}", type="primary"):
            run(lambda db: admin_advance(db, admin, k, nxt[0], note), "Order updated.")
    if o.payment_status in ("cod", "pending") and o.status != "cancelled":
        ref = st.text_input("Payment reference (optional)", key=f"pr_{k}", max_chars=40)
        if st.button("Mark payment received", key=f"pay_{k}"):
            run(lambda db: admin_mark_paid(db, admin, k, ref), "Payment recorded.")
    if o.status in ("in_lab", "report_ready"):
        up = st.file_uploader("Report PDF", type=["pdf"], key=f"up_{k}")
        if up is not None and st.button("Upload report", key=f"upb_{k}", type="primary"):
            run(lambda db: admin_upload_report(db, admin, k, up.name, up.getvalue()), "Report uploaded.")
    note2 = st.text_input("Internal note", key=f"note_{k}", max_chars=280)
    if st.button("Add note", key=f"noteb_{k}") and note2.strip():
        run(lambda db: admin_add_note(db, admin, k, note2), "Note added.")
    if "cancelled" in TRANSITIONS.get(o.status, set()):
        with st.expander("Cancel this order"):
            reason = st.text_input("Reason (shown to the customer)", key=f"cr_{k}", max_chars=200)
            sure = st.checkbox("I'm sure. This frees the slot and refunds any payment.", key=f"cs_{k}")
            if st.button("Cancel order", key=f"cb_{k}") and sure:
                run(lambda db: admin_cancel(db, admin, k, reason), "Order cancelled.")


def page_admin_orders() -> None:
    admin = _admin()
    if not admin:
        return
    st.title("Orders")
    with session_scope() as db:
        expire_unpaid_orders(db)
        cities = _cities(db)
    c1, c2, c3 = st.columns([2, 2, 3])
    status_label = c1.selectbox("Status", ["All"] + [STATUS_LABELS[x] for x in ORDER_STATUSES], key="ao_status")
    city = c2.selectbox("City", ["All"] + cities, key="ao_city")
    q = c3.text_input("Search order number, name or phone", key="ao_q")
    by_date = st.toggle("Filter by collection date", key="ao_bydate")
    day_from = day_to = None
    if by_date:
        picked = st.date_input("Collection dates", value=(local_now().date(), local_now().date()), key="ao_dates")
        if isinstance(picked, (list, tuple)) and len(picked) == 2:
            day_from, day_to = picked
    status = next((k for k, v in STATUS_LABELS.items() if v == status_label), None)
    with session_scope() as db:
        rows = admin_list_orders(db, admin, status=status, city=None if city == "All" else city,
                                 day_from=day_from, day_to=day_to, q=q)
    st.caption(f"{len(rows)} order(s)")
    _table(rows, "No orders match these filters.")
    if rows:
        _export("Prepare CSV of these orders", "ao_export", lambda: rows_to_csv(rows), "orders.csv")
        chosen = st.selectbox("Open an order", [r["Order"] for r in rows], key="ao_open",
                              format_func=lambda n: next(f"{r['Order']}: {r['Customer']} ({r['Status']})" for r in rows if r["Order"] == n))
        st.divider()
        _admin_order_panel(admin, chosen)


def page_admin_runsheet() -> None:
    admin = _admin()
    if not admin:
        return
    st.title("Collection run sheet")
    with session_scope() as db:
        cities = _cities(db)
    c1, c2 = st.columns(2)
    day = c1.date_input("Day", value=local_now().date(), key="rs_day")
    city = c2.selectbox("City", ["All"] + cities, key="rs_city")
    with session_scope() as db:
        rows = admin_runsheet(db, admin, day, None if city == "All" else city)
    unassigned = sum(1 for r in rows if r["Collector"] == "UNASSIGNED")
    st.caption(f"{len(rows)} collection(s)" + (f", {unassigned} still need a collector" if unassigned else ""))
    _table(rows, "No collections planned for this day.")
    if rows:
        by_collector = Counter(r["Collector"] for r in rows)
        st.subheader("Workload by collector")
        _table([{"Collector": k, "Collections": v, "Cash to collect (₹)": sum(r["Collect cash (₹)"] for r in rows if r["Collector"] == k)}
                for k, v in by_collector.items()])

        def make() -> str:
            with session_scope() as db:
                return rows_to_csv(admin_runsheet(db, admin, day, None if city == "All" else city, export=True))
        _export("Prepare CSV for collectors (contains phone numbers; the export is logged)", "rs_export", make,
                f"runsheet_{day}.csv")


def page_admin_catalogue() -> None:
    admin = _admin()
    if not admin:
        return
    st.title("Tests and panels")
    tab_t, tab_p = st.tabs(["Tests", "Panels"])
    with tab_t:
        with session_scope() as db:
            tests = admin_list_tests(db, admin)
            snap = {t.code: t for t in tests}
            rows = [{"Code": t.code, "Name": t.name, "Category": t.category, "Price (₹)": t.price, "MRP (₹)": t.mrp,
                     "Fasting (h)": t.fasting_hours, "Report (h)": t.tat_hours, "Popular": t.popular, "Active": t.active}
                    for t in tests]
        _table(rows)
        sel = st.selectbox("Edit a test", ["+ New test"] + list(snap), key="cat_test_sel",
                           format_func=lambda c: c if c.startswith("+") else f"{c}: {snap[c].name}")
        cur = snap.get(sel)
        with st.form(f"test_form_{sel}"):
            code = st.text_input("Code", value=cur.code if cur else "", disabled=bool(cur), max_chars=30)
            name = st.text_input("Name", value=cur.name if cur else "", max_chars=120)
            category = st.text_input("Organ or site", value=cur.category if cur else "", max_chars=40)
            description = st.text_area("Description", value=cur.description if cur else "", max_chars=600)
            sample = st.text_input("Sample type", value=cur.sample_type if cur else "Serum", max_chars=30)
            n1, n2, n3, n4 = st.columns(4)
            price = n1.number_input("Price (₹)", min_value=1, value=cur.price if cur else 500, step=10)
            mrp = n2.number_input("MRP (₹)", min_value=1, value=cur.mrp if cur else 900, step=10)
            fasting = n3.number_input("Fasting hours", min_value=0, max_value=24, value=cur.fasting_hours if cur else 0)
            tat = n4.number_input("Report in (hours)", min_value=1, max_value=240, value=cur.tat_hours if cur else 24)
            prep = st.text_area("Preparation notes (shown to customers)", value=cur.prep_notes if cur else "", max_chars=600)
            interf = st.text_area("Things that can affect the result", value=cur.interference_notes if cur else "", max_chars=600)
            popular = st.checkbox("Popular", value=cur.popular if cur else False)
            active = st.checkbox("Active (visible and bookable)", value=cur.active if cur else True)
            if st.form_submit_button("Save test", type="primary"):
                try:
                    with session_scope() as db:
                        admin_save_test(db, admin, code=cur.code if cur else code, name=name, category=category,
                                        description=description, sample_type=sample, fasting_hours=fasting, tat_hours=tat,
                                        price=price, mrp=mrp, prep_notes=prep, interference_notes=interf,
                                        popular=popular, active=active)
                    flash("Test saved.")
                    st.rerun()
                except ServiceError as exc:
                    st.error(str(exc))
        st.caption("Tests are never deleted: switch off Active to hide one. Past orders keep the name and price they were booked at.")
    with tab_p:
        with session_scope() as db:
            pkgs = admin_list_packages(db, admin)
            psnap = {p.code: p for p in pkgs}
            prows = [{"Code": p.code, "Name": p.name, "For": p.audience, "Price (₹)": p.price, "MRP (₹)": p.mrp,
                      "Tests": ", ".join(t.code for t in p.tests), "Active": p.active} for p in pkgs]
            all_codes = [t.code for t in admin_list_tests(db, admin)]
        _table(prows)
        sel = st.selectbox("Edit a panel", ["+ New panel"] + list(psnap), key="cat_pkg_sel",
                           format_func=lambda c: c if c.startswith("+") else f"{c}: {psnap[c].name}")
        cur = psnap.get(sel)
        with st.form(f"pkg_form_{sel}"):
            code = st.text_input("Code", value=cur.code if cur else "", disabled=bool(cur), max_chars=30)
            name = st.text_input("Name", value=cur.name if cur else "", max_chars=120)
            description = st.text_area("Description", value=cur.description if cur else "", max_chars=600)
            audience = st.selectbox("Designed for", ["all", "male", "female"],
                                    index=["all", "male", "female"].index(cur.audience) if cur else 0)
            n1, n2 = st.columns(2)
            price = n1.number_input("Price (₹)", min_value=1, value=cur.price if cur else 1500, step=50)
            mrp = n2.number_input("MRP (₹)", min_value=1, value=cur.mrp if cur else 2500, step=50)
            members = st.multiselect("Tests included (at least two)", all_codes, default=[t.code for t in cur.tests] if cur else [])
            popular = st.checkbox("Popular", value=cur.popular if cur else False)
            active = st.checkbox("Active", value=cur.active if cur else True)
            if st.form_submit_button("Save panel", type="primary"):
                try:
                    with session_scope() as db:
                        admin_save_package(db, admin, code=cur.code if cur else code, name=name, description=description,
                                           audience=audience, price=price, mrp=mrp, popular=popular, active=active,
                                           test_codes=members)
                    flash("Panel saved.")
                    st.rerun()
                except ServiceError as exc:
                    st.error(str(exc))


def page_admin_locations() -> None:
    admin = _admin()
    if not admin:
        return
    st.title("Locations and demand")
    tab_pin, tab_wait = st.tabs(["Serviceable pincodes", "Demand (waitlist)"])
    with tab_pin:
        q = st.text_input("Search by pincode, area or city", key="loc_q")
        with session_scope() as db:
            rows = admin_list_pincodes(db, admin, q)
        st.caption(f"{len(rows)} pincode(s) shown (max 500)")
        _table(rows)
        with st.form("pin_form"):
            st.markdown("**Add or update a pincode**")
            c1, c2, c3 = st.columns(3)
            pin = c1.text_input("Pincode", max_chars=6)
            area = c2.text_input("Area (optional)", max_chars=80)
            city = c3.text_input("City", max_chars=80)
            c4, c5, c6 = st.columns(3)
            state = c4.text_input("State", max_chars=80)
            fee = c5.number_input("Collection fee (₹)", min_value=0, max_value=1000, value=0)
            active = c6.checkbox("Serviceable now", value=True, help="Untick for 'coming soon'")
            if st.form_submit_button("Save pincode", type="primary"):
                try:
                    with session_scope() as db:
                        admin_save_pincode(db, admin, pincode=pin, area=area, city=city, state=state, active=active, fee=fee)
                    flash("Pincode saved.")
                    st.rerun()
                except ServiceError as exc:
                    st.error(str(exc))
        with st.expander("Bulk import from CSV"):
            st.caption("Header row: pincode,area,city,state,active,collection_fee (only pincode, city and state are required). "
                       "The India Post directory is available from data.gov.in.")
            up = st.file_uploader("CSV file", type=["csv"], key="pin_csv")
            if up is not None and st.button("Import pincodes", key="pin_import"):
                try:
                    with session_scope() as db:
                        ok, errors = admin_import_pincodes(db, admin, up.getvalue().decode("utf-8", errors="replace"))
                    st.success(f"Imported {ok} pincode(s).")
                    for e in errors[:20]:
                        st.warning(e)
                    if len(errors) > 20:
                        st.warning(f"...and {len(errors) - 20} more rows were skipped.")
                except ServiceError as exc:
                    st.error(str(exc))
    with tab_wait:
        st.caption("Where customers are asking for service. Launch the busiest pincodes first, then clear the list after you notify them.")
        with session_scope() as db:
            wl = admin_waitlist(db, admin)
        _table(wl, "Nobody is waiting.")
        if wl:
            pin = st.selectbox("Pincode", [w["Pincode"] for w in wl], key="wl_pin")
            if st.button("Clear this pincode's waitlist (after notifying)", key="wl_clear"):
                with session_scope() as db:
                    n = admin_clear_waitlist(db, admin, pin)
                flash(f"Cleared {n} request(s).")
                st.rerun()


def _parse_windows(text: str) -> list[tuple[str, str]]:
    out = []
    for part in text.split(","):
        if part.strip():
            a, _, b = part.strip().partition("-")
            out.append((a.strip(), b.strip()))
    return out


def page_admin_slots() -> None:
    admin = _admin()
    if not admin:
        return
    st.title("Collection slots")
    today = local_now().date()
    with session_scope() as db:
        cities = _cities(db)
    c1, c2, c3 = st.columns(3)
    city = c1.selectbox("City", ["All"] + cities, key="sl_city")
    d1 = c2.date_input("From", value=today, key="sl_from")
    d2 = c3.date_input("To", value=today + timedelta(days=7), key="sl_to")
    with session_scope() as db:
        slots = admin_list_slots(db, admin, None if city == "All" else city, d1, d2)
    _table([{"ID": s_.id, "City": s_.city, "Day": f"{s_.day:%a %d %b}", "Window": s_.label, "Booked": s_.booked,
             "Capacity": s_.capacity, "Free": s_.remaining, "Open": s_.active} for s_ in slots], "No slots in this range.")
    if slots:
        sel = st.selectbox("Edit a slot", [s_.id for s_ in slots], key="sl_edit",
                           format_func=lambda i: next(f"{s_.city} {s_.day:%a %d %b} {s_.label}" for s_ in slots if s_.id == i))
        cur = next(s_ for s_ in slots if s_.id == sel)
        with st.form(f"slot_form_{sel}"):
            cap = st.number_input("Capacity", min_value=1, max_value=500, value=cur.capacity)
            active = st.checkbox("Open for new bookings", value=cur.active)
            if st.form_submit_button("Save slot"):
                try:
                    with session_scope() as db:
                        admin_update_slot(db, admin, sel, capacity=cap, active=active)
                    flash("Slot updated.")
                    st.rerun()
                except ServiceError as exc:
                    st.error(str(exc))
    st.divider()
    with st.form("slot_gen"):
        st.markdown("**Generate slots**  \nCreates only the missing ones. Existing slots and bookings are never changed.")
        g1, g2 = st.columns(2)
        gcity = g1.text_input("City", value=cities[0] if cities else "", max_chars=80)
        gcap = g2.number_input("Capacity per slot", min_value=1, max_value=500, value=6)
        g3, g4 = st.columns(2)
        gfrom = g3.date_input("First day", value=today + timedelta(days=1))
        gto = g4.date_input("Last day", value=today + timedelta(days=14))
        wins = st.text_input("Time windows", value="06:00-08:00, 08:00-10:00, 10:00-12:00",
                             help="Comma-separated, 24-hour HH:MM-HH:MM")
        sundays = st.checkbox("Skip Sundays")
        if st.form_submit_button("Generate", type="primary"):
            try:
                with session_scope() as db:
                    created, existed = admin_generate_slots(db, admin, city=gcity, start_day=gfrom, end_day=gto,
                                                            windows=_parse_windows(wins), capacity=gcap, skip_sundays=sundays)
                flash(f"Created {created} slot(s). {existed} already existed.")
                st.rerun()
            except ServiceError as exc:
                st.error(str(exc))


def page_admin_team() -> None:
    admin = _admin()
    if not admin:
        return
    st.title("Collectors")
    with session_scope() as db:
        rows = admin_list_phlebotomists(db, admin)
        cities = _cities(db)
    _table(rows, "No collectors yet.")
    sel = st.selectbox("Edit a collector", [0] + [r["ID"] for r in rows], key="tm_sel",
                       format_func=lambda i: "+ New collector" if i == 0 else next(f"{r['Name']} ({r['City']})" for r in rows if r["ID"] == i))
    cur = next((r for r in rows if r["ID"] == sel), None)
    with st.form(f"tm_form_{sel}"):
        name = st.text_input("Name", value=cur["Name"] if cur else "", max_chars=120)
        phone = st.text_input("Mobile", value=cur["Phone"] if cur else "", max_chars=16)
        city = st.text_input("City", value=cur["City"] if cur else (cities[0] if cities else ""), max_chars=80,
                             help="Must match the city name used in Locations")
        active = st.checkbox("Active", value=cur["Active"] if cur else True)
        if st.form_submit_button("Save collector", type="primary"):
            try:
                with session_scope() as db:
                    admin_save_phlebotomist(db, admin, phlebotomist_id=sel or None, name=name, phone=phone, city=city, active=active)
                flash("Collector saved.")
                st.rerun()
            except ServiceError as exc:
                st.error(str(exc))


def page_admin_coupons() -> None:
    admin = _admin()
    if not admin:
        return
    st.title("Coupons")
    with session_scope() as db:
        coupons = admin_list_coupons(db, admin)
    snap = {c.code: c for c in coupons}
    _table([{"Code": c.code, "Type": c.kind, "Value": c.value, "Min order (₹)": c.min_order,
             "Cap (₹)": c.max_discount or "", "Valid": f"{c.valid_from or '…'} to {c.valid_to or '…'}",
             "Used": f"{c.used_count}/{c.usage_limit or '∞'}", "Per customer": c.per_user_limit, "Active": c.active}
            for c in coupons], "No coupons yet.")
    sel = st.selectbox("Edit a coupon", ["+ New coupon"] + list(snap), key="cp_sel")
    cur = snap.get(sel)
    with st.form(f"cp_form_{sel}"):
        code = st.text_input("Code", value=cur.code if cur else "", disabled=bool(cur), max_chars=30)
        c1, c2, c3 = st.columns(3)
        kind = c1.selectbox("Type", ["percent", "flat"], index=["percent", "flat"].index(cur.kind) if cur else 0)
        value = c2.number_input("Value (% or ₹)", min_value=1, value=cur.value if cur else 10)
        minimum = c3.number_input("Minimum order (₹)", min_value=0, value=cur.min_order if cur else 0)
        c4, c5, c6 = st.columns(3)
        cap = c4.number_input("Max discount ₹ (0 = none)", min_value=0, value=(cur.max_discount or 0) if cur else 0)
        limit = c5.number_input("Total uses (0 = unlimited)", min_value=0, value=(cur.usage_limit or 0) if cur else 0)
        per_user = c6.number_input("Uses per customer", min_value=1, value=cur.per_user_limit if cur else 1)
        c7, c8 = st.columns(2)
        vfrom = c7.date_input("Valid from (optional)", value=cur.valid_from if cur else None)
        vto = c8.date_input("Valid until (optional)", value=cur.valid_to if cur else None)
        active = st.checkbox("Active", value=cur.active if cur else True)
        if st.form_submit_button("Save coupon", type="primary"):
            try:
                with session_scope() as db:
                    admin_save_coupon(db, admin, code=cur.code if cur else code, kind=kind, value=value, min_order=minimum,
                                      max_discount=cap or None, valid_from=vfrom, valid_to=vto, usage_limit=limit or None,
                                      per_user_limit=per_user, active=active)
                flash("Coupon saved.")
                st.rerun()
            except ServiceError as exc:
                st.error(str(exc))


def page_admin_customers() -> None:
    admin = _admin()
    if not admin:
        return
    st.title("Customers")
    q = st.text_input("Search by name, phone or email", key="cu_q")
    with session_scope() as db:
        rows = admin_search_customers(db, admin, q)
    st.caption(f"{len(rows)} account(s). Phone numbers are masked here; opening a customer shows full details and is logged.")
    _table(rows, "No customers match.")
    if not rows:
        return
    uid = st.selectbox("Open a customer", [r["ID"] for r in rows], key="cu_open",
                       format_func=lambda i: next(f"{r['Name']} ({r['Phone']})" for r in rows if r["ID"] == i))
    if not st.button("Show details", key="cu_show") and st.session_state.get("cu_shown") != uid:
        return
    st.session_state["cu_shown"] = uid
    with session_scope() as db:
        d = admin_customer_detail(db, admin, uid)
    st.subheader(d["name"] or "(profile incomplete)")
    st.markdown(f"**Phone:** {d['phone']}  \n**Email:** {esc(d['email'] or '')}  \n**Born:** {d['dob'] or ''}, {d['sex'] or ''}  \n"
                f"**Pincode:** {d['pincode'] or ''}  \n**Role:** {d['role']}, **{'active' if d['active'] else 'disabled'}**  \n"
                f"**Joined:** {d['joined']}, last sign-in {d['last_login'] or 'never'}")
    st.markdown("**Consents on record**")
    _table(d["consents"], "None recorded.")
    st.markdown("**People on this account**")
    _table([{"Name": p.name, "Relation": p.relation, "Sex": p.sex, "Born": f"{p.dob:%d %b %Y}"} for p in d["family"]])
    st.markdown("**Orders**")
    _table(d["orders"], "No orders.")
    c1, c2 = st.columns(2)
    if c1.button("Disable account" if d["active"] else "Enable account", key=f"cu_act_{uid}"):
        try:
            with session_scope() as db:
                admin_set_user_active(db, admin, uid, not d["active"])
            flash("Account updated." + (" They've been signed out everywhere." if d["active"] else ""))
            st.rerun()
        except ServiceError as exc:
            st.error(str(exc))
    role = c2.selectbox("Role", ["customer", "admin"], index=["customer", "admin"].index(d["role"]) if d["role"] in ("customer", "admin") else 0,
                        key=f"cu_role_{uid}")
    if role != d["role"] and c2.button("Change role", key=f"cu_rolebtn_{uid}"):
        try:
            with session_scope() as db:
                admin_set_role(db, admin, uid, role)
            flash("Role updated.")
            st.rerun()
        except ServiceError as exc:
            st.error(str(exc))


def page_admin_audit() -> None:
    admin = _admin()
    if not admin:
        return
    st.title("Audit log")
    st.caption("Who did what, and when. Phone numbers are never written here.")
    with session_scope() as db:
        actions = admin_audit_actions(db, admin)
    action = st.selectbox("Action", ["All"] + actions, key="au_action")
    with session_scope() as db:
        rows = admin_audit_log(db, admin, None if action == "All" else action)
    st.caption(f"Latest {len(rows)} entries")
    _table(rows, "Nothing logged yet.")
    if rows:
        st.download_button("Download CSV", rows_to_csv(rows), file_name="audit_log.csv", mime="text/csv", key="au_dl")


# ======================================================================================
# 7. ENTRY POINT
# ======================================================================================

def schema_problem() -> str | None:
    """create_all() never alters existing tables. Detect a database file made by an older version."""
    insp = inspect(_engine)
    for table in Base.metadata.sorted_tables:
        if insp.has_table(table.name):
            missing = {c.name for c in table.columns} - {c["name"] for c in insp.get_columns(table.name)}
            if missing:
                return (f"The database was created by an older version of this app (table '{table.name}' is missing "
                        f"{sorted(missing)}). Delete the database file (marker_booking.db) or reset your hosted "
                        "database, then restart. Proper migrations (Alembic) are on the roadmap.")
    return None


@st.cache_resource(show_spinner=False)
def bootstrap() -> str | None:
    """Validate config, create tables, seed data. Returns an error message if startup is unsafe."""
    try:
        settings = get_settings()
    except ConfigError as exc:
        return str(exc)
    init_engine()
    problem = schema_problem()
    if problem:
        return problem
    Base.metadata.create_all(_engine)
    with session_scope() as db:
        seed_all(db)
        if settings.app_env != "production":
            seed_demo_data(db)
        expire_unpaid_orders(db)
    return None


def main() -> None:
    st.set_page_config(page_title=f"{BRAND}: cancer marker tests at home", page_icon="🩺", layout="centered")
    st.markdown(CSS, unsafe_allow_html=True)
    error = bootstrap()
    if error:
        st.error(error)
        st.stop()

    user = current_user()
    authenticated = is_authenticated(user)
    pages = {
        "home": st.Page(page_home, title="Home", icon=":material/home:", url_path="home", default=True),
        "tests": st.Page(page_tests, title="Tests", icon=":material/biotech:", url_path="tests"),
        "cart": st.Page(page_cart, title="Cart", icon=":material/shopping_cart:", url_path="cart"),
    }
    if authenticated:
        pages["orders"] = st.Page(page_orders, title="My orders", icon=":material/receipt_long:", url_path="orders")
        pages["account"] = st.Page(page_account, title="My account", icon=":material/person:", url_path="account")
    else:
        pages["login"] = st.Page(page_login, title="Sign in", icon=":material/login:", url_path="sign-in")
    admin_pages = []
    if authenticated and user.role == "admin":
        admin_pages = [
            st.Page(page_admin_overview, title="Overview", icon=":material/dashboard:", url_path="admin"),
            st.Page(page_admin_orders, title="Orders", icon=":material/inventory_2:", url_path="admin-orders"),
            st.Page(page_admin_runsheet, title="Run sheet", icon=":material/route:", url_path="admin-runsheet"),
            st.Page(page_admin_catalogue, title="Tests & panels", icon=":material/biotech:", url_path="admin-catalogue"),
            st.Page(page_admin_locations, title="Locations", icon=":material/location_on:", url_path="admin-locations"),
            st.Page(page_admin_slots, title="Slots", icon=":material/schedule:", url_path="admin-slots"),
            st.Page(page_admin_team, title="Collectors", icon=":material/badge:", url_path="admin-collectors"),
            st.Page(page_admin_coupons, title="Coupons", icon=":material/sell:", url_path="admin-coupons"),
            st.Page(page_admin_customers, title="Customers", icon=":material/groups:", url_path="admin-customers"),
            st.Page(page_admin_audit, title="Audit log", icon=":material/history:", url_path="admin-audit"),
        ]
    PAGES.clear()
    PAGES.update(pages)

    render_header()
    show_flash()
    structure = {"Shop": list(pages.values()), "Admin": admin_pages} if admin_pages else list(pages.values())
    try:
        nav = st.navigation(structure, position="top")
    except TypeError:  # older Streamlit without top navigation
        nav = st.navigation(structure)
    nav.run()
    st.markdown(f'<div class="cm-footer">{esc(BRAND)} is a demonstration build. Prices and turnaround times are '
                "illustrative. Reports must come from an accredited laboratory.</div>", unsafe_allow_html=True)


if __name__ == "__main__":
    main()
