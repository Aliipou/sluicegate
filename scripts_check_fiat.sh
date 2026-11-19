#!/bin/sh
# T4: fail unless the fiat-crypto backend is selected for curve25519-dalek.
cd "$(dirname "$0")/authgate-kernel" || exit 2
if cargo tree -i fiat-crypto >/dev/null 2>&1; then echo "OK: fiat backend selected"; else echo "FAIL: fiat backend NOT selected (RUSTFLAGS override?)"; exit 1; fi
