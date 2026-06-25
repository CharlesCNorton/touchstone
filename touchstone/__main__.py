"""`python -m touchstone` runs the self-tests and the demonstration; `python -m touchstone
<command> ...` runs a command-line verb (see `touchstone -h` or `python -m touchstone check -h`)."""
import sys

if __name__ == "__main__":
    if len(sys.argv) > 1:
        from .cli import main
        raise SystemExit(main())
    from ._impl import run_self_tests, demo
    run_self_tests()
    demo()
