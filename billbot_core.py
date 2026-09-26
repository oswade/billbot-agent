"""Flat compatibility loader for the BillBot pricing engine.

The deterministic BillBot pricing core is kept in ``billbot_engine_core.py``.
This loader redirects resource paths so the complete Grok package can remain
flat, with ``aer_seasonality_2021.json`` at the repository root.
"""
from __future__ import annotations
import os
import billbot_engine_core as _core

_ROOT = os.path.dirname(__file__)
_core.DATA_DIR = _ROOT
_core.RETAILERS_PATH = os.path.join(_ROOT, "retailers.json")
_core.SEASONALITY_PATH = os.path.join(_ROOT, "aer_seasonality_2021.json")

# Re-export the BillBot pricing-core API.
for _name in dir(_core):
    if not _name.startswith("__"):
        globals()[_name] = getattr(_core, _name)
