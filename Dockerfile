# Reproducible build: the self-tests and four soundness audits on a pinned Python + z3 +
# cvc5 stack.   docker build -t touchstone .   &&   docker run --rm touchstone   (tail: "CI OK")
# The Rocq/SMTCoq proofs in proofs/ are checked separately (see proofs/toolchain.lock).
FROM python:3.13.2-slim

WORKDIR /work
COPY pyproject.toml README.md ./
COPY touchstone/ ./touchstone/
RUN pip install --no-cache-dir .

CMD ["python", "-m", "touchstone.ci"]
