#!/bin/sh
# T8: trace validation of the Rust gate against formal/AuthGateV3.tla.
#   1. run cargo tests with `--features trace`, collecting JSON-lines traces
#   2. validate every trace with TLC (TraceAuthGateV3.tla)
#   3. mutate an accepted trace (flip a Permit decision to Deny): TLC must REJECT it
# PASS iff: validated >= MIN_TRACES (default 20) AND mutated trace rejected AND no TLC errors.
# Not a refinement proof; checks only the collected test traces. Traces that
# TLC rejects are listed (they are divergences between Rust and the TLA+ model).
# Env: TLA2TOOLS (path to tla2tools.jar), TRACE_DIR (reuse existing traces; skips cargo),
#      MIN_TRACES, LIMIT (max traces validated, default 40, 0 = all), CARGO_TARGET_DIR.
set -u
ROOT=$(cd "$(dirname "$0")/.." && pwd)
FORMAL="$ROOT/formal"
JAR=${TLA2TOOLS:-$FORMAL/tla2tools.jar}
[ -f "$JAR" ] || { echo "FAIL: tla2tools.jar not found (set TLA2TOOLS)"; exit 2; }

check() { # $1 = trace file; prints ACCEPT | REJECT | ERROR
  d=$(mktemp -d)
  cp "$FORMAL/AuthGateV3.tla" "$FORMAL/TraceAuthGateV3.tla" "$FORMAL/TraceAuthGateV3.cfg" "$d/"
  cp "$1" "$d/trace.jsonl"
  out=$(cd "$d" && java -Xmx512m -XX:+UseParallelGC -jar "$JAR" -config TraceAuthGateV3.cfg -workers 1 -metadir "$d/m" TraceAuthGateV3.tla 2>&1)
  if echo "$out" | grep -q "No error has been found"; then echo ACCEPT
  elif echo "$out" | grep -q "Temporal propert.* violated"; then echo REJECT
  else echo ERROR; echo "$out" | grep -i "error" | head -3 >&2; fi
  rm -rf "$d"
}
if [ "${1:-}" = "--one" ]; then echo "$(check "$2") $(basename "$2")"; exit 0; fi

MIN_TRACES=${MIN_TRACES:-20}
WORK=$(mktemp -d)
echo "workdir: $WORK"
TRACE_DIR=${TRACE_DIR:-$WORK/traces}
if [ ! -d "$TRACE_DIR" ]; then
  mkdir -p "$TRACE_DIR"
  (cd "$ROOT/authgate-kernel" && AUTHGATE_TRACE_DIR="$TRACE_DIR" cargo test --lib --features trace >"$WORK/cargo.log" 2>&1) \
    || { echo "FAIL: cargo test (see $WORK/cargo.log)"; exit 2; }
fi
export TLA2TOOLS="$JAR"

: >"$WORK/results.txt"
n=0
for f in "$TRACE_DIR"/*.jsonl; do
  case "$f" in */skipped.jsonl) continue;; esac
  grep -q '"kind":"verify"' "$f" || continue
  [ "${LIMIT:-40}" -gt 0 ] && [ "$n" -ge "${LIMIT:-40}" ] && break
  n=$((n+1))
  echo "$(check "$f") $(basename "$f")" >>"$WORK/results.txt"
done

ok=$(grep -c '^ACCEPT' "$WORK/results.txt"); rej=$(grep -c '^REJECT' "$WORK/results.txt"); err=$(grep -c '^ERROR' "$WORK/results.txt")
echo "validated=$ok rejected(non-conforming)=$rej tlc_errors=$err (need >= $MIN_TRACES validated)"
grep -v '^ACCEPT' "$WORK/results.txt" | sed 's/^/  /'

# Mutation: flip the first Permit decision to Deny in an accepted trace; must be REJECTED.
first=""
for f in $(grep -l '"decision":"Permit"' "$TRACE_DIR"/*.jsonl); do
  if grep -q "^ACCEPT $(basename "$f")\$" "$WORK/results.txt"; then first="$f"; break; fi
done
mut=FAIL
if [ -n "$first" ]; then
  sed '0,/"decision":"Permit"/s//"decision":"Deny"/' "$first" >"$WORK/mutated.jsonl"
  echo "mutating $(basename "$first")"
  [ "$(check "$WORK/mutated.jsonl")" = REJECT ] && mut=ok
fi
echo "mutated trace rejected: $mut"
if [ "$ok" -ge "$MIN_TRACES" ] && [ "$mut" = ok ] && [ "$err" -eq 0 ]; then echo "PASS"; exit 0; fi
echo "CHECK FAILED"; exit 1
