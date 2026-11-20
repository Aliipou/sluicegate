#!/bin/sh
# T4: fail unless curve25519-dalek's fiat-crypto backend is selected for authgate-kernel.
# A RUSTFLAGS env var REPLACES .cargo/config.toml rustflags, silently deselecting fiat;
# `cargo tree` honours RUSTFLAGS, so this check catches that case too.
cd "$(dirname "$0")/authgate-kernel" || exit 2
if cargo tree -i fiat-crypto 2>/dev/null | grep -q '^fiat-crypto'; then
  echo "OK: fiat backend selected"
else
  echo "FAIL: fiat backend NOT selected (RUSTFLAGS='${RUSTFLAGS}' overrides config?)"; exit 1
fi
