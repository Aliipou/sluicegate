# formal/verus (T9 pilot: one property)

Verus proof, on a copy of the dag.rs rights/attenuation logic (not linked to the TCB build), that the
delegation walk never escalates rights over chains of arbitrary length and any depth limit
(loop invariant + ghost path; no unrolling). Mirror of `formal/kani/prop_chain.rs::proof_attenuation_two_node`.

Check (WSL2 Ubuntu, Verus release 0.2026.11.02.8bf68ee, x86-linux zip from github.com/verus-lang/verus):

    verus --crate-type=lib src/main.rs      # or: verus src/main.rs

Trusted assumptions are listed at the top of `src/main.rs` (A1-A4: crypto/epoch/resource checks abstracted away,
u64 hashes, hand-copied loop, depth limit generic). No assume/admit/external_body is used.

STATUS: written but NOT yet machine-checked, see status/T9.md.
