#!/bin/bash
# usage: ./run.sh   (needs tamarin-prover 1.12.0 + maude on PATH)
T=${TAMARIN:-tamarin-prover}
for v in "" "-DSHAREDKEY" "-DSHAREDKEY -DTAGGED"; do
  echo "=== variant: ${v:-separate-keys, untagged}"
  $T $v --prove delegation_audit.spthy 2>&1 | sed -n '/summary of summaries/,$p' | grep -E "verified|falsified|processing time"
done
