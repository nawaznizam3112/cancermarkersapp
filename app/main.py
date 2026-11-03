"""Entry point:  streamlit run app/main.py"""
from __future__ import annotations

import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

import streamlit as st  # noqa: E402

from app import registry, state  # noqa: E402
from app.bootstrap import bootstrap  # noqa: E402
from app.ui import theme  # noqa: E402
from app.views import account, catalogue, home, login  # noqa: E402

st.set_page_config(page_title=f"{theme.BRAND}: cancer marker tests at home", page_icon="🩺", layout="centered")
theme.inject_css()

error = bootstrap()
if error:
    st.error(error)
    st.stop()


def _header(authenticated: bool) -> None:
    left, mid, right = st.columns([3, 3, 2], vertical_alignment="center")
    left.markdown(f'<p class="cm-brand">{theme.esc(theme.BRAND)}<span>.</span></p>', unsafe_allow_html=True)
    info = state.get_pincode_info()
    label = f"Pincode {info.pincode}" if info else "Set pincode"
    with mid.popover(label, icon=":material/location_on:"):
        from app.ui.components import pincode_result
        from core.db import session_scope
        from core.errors import ServiceError
        from core.services import pincode_service

        state.sync_pincode_input("header_pincode")
        with st.form("header_pincode_form"):
            pin = st.text_input("Pincode", key="header_pincode", max_chars=6)
            if st.form_submit_button("Check"):
                try:
                    with session_scope() as db:
                        state.set_pincode_info(pincode_service.check_pincode(db, pin), "header_pincode")
                    st.rerun()
                except ServiceError as exc:
                    st.error(str(exc))
        if info:
            pincode_result(info, key="header")


user = state.current_user()
authenticated = state.is_authenticated(user)

pages = {
    "home": st.Page(home.render, title="Home", icon=":material/home:", url_path="home", default=True),
    "tests": st.Page(catalogue.render, title="Tests", icon=":material/biotech:", url_path="tests"),
}
if authenticated:
    pages["account"] = st.Page(account.render, title="My account", icon=":material/person:", url_path="account")
else:
    pages["login"] = st.Page(login.render, title="Sign in", icon=":material/login:", url_path="sign-in")
registry.PAGES.clear()
registry.PAGES.update(pages)

_header(authenticated)
try:
    nav = st.navigation(list(pages.values()), position="top")
except TypeError:  # older Streamlit without top navigation
    nav = st.navigation(list(pages.values()))
nav.run()
theme.footer()
