"""Verified-extraction modules, generated -- not written by hand. Each `*_rocq.py` here is the mechanical
Python image of a Rocq development in ../../proofs, produced by proofs/json_to_python.py from the JSON
abstract syntax that the same extraction pipeline lowers to OCaml. `vcgen_rocq` is the weakest-precondition
VC generator proved sound and complete in touchstone_functor.v; `intervals_rocq` the interval operators
proved sound in touchstone_domains.v; `encoding_rocq` the //,% encoding proved equal to Python's in
touchstone_encoding.v. Regenerate with proofs/generate_engine.sh; verify_coq.sh checks these match a fresh
generation, and the engine's extracted_* audits check them equal to the OCaml extraction."""
