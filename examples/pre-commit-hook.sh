#!/usr/bin/env bash
# Touchstone gate as a git pre-commit hook: before a commit is allowed, verify that each changed function
# preserves its properties (an @ensure contract if present, otherwise its behavior, and trap freedom for a
# new function), and reject the commit with a counterexample if a change breaks one.
#
# Install:  cp examples/pre-commit-hook.sh .git/hooks/pre-commit && chmod +x .git/hooks/pre-commit
# Requires: pip install touchstone-prover
exec touchstone gate . --base HEAD
