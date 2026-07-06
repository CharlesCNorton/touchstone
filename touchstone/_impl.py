"""Aggregator: the implementation now lives in the focused modules core, engines, domains,
theories, and audit. This module preserves the historical touchstone._impl import surface."""
from . import core, engines, domains, vcgen, audit, inference
from .core import *
from .engines import *
from .domains import *
from .vcgen import *
from .audit import *
from .inference import infer_return_type, infer_local_types, infer_types
from .core import ALLOW_SUBJECT_EXECUTION, REQUIRE_CORROBORATION, CROSS_VALIDATE_DOMAINS
from .vcgen import proof_bundle, recheck_bundle
from .repro import repro_test
from .diagnostics import classify_unknown, advice, budget_helps, capabilities
