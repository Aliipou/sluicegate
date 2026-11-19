# Robust safety: statement shapes and the Iris signature idiom

Sources (statements read from the PDFs, text-extracted; Greek/logic symbols
were lost in extraction, so formulas below are paraphrased from the surrounding
prose and rule names, not copied symbol-for-symbol):
- OCPL: Swasey, Garg, Dreyer, OOPSLA 2017 (PACMPL 1, art. 89), full version
  https://people.mpi-sws.org/~dg/papers/oopsla17-obj-full.pdf (DOI 10.1145/3133913)
- Cerise: Georges et al., JACM 71(1), 2024 (DOI 10.1145/3623510), preprint
  https://cs.au.dk/~birke/papers/cerise.pdf

## 1. OCPL (Sec. 2.3, "Theorem RobustSafety")
Shape: for every adversarial context C in AdvCtx (HLA contexts containing no
assertions and no heap locations), every closed e with a verified spec
`{True} e {x. lowval x}` (progressive triple), and every run
`(C[e]); (empty heap, OK) ->* (h, goodness)`, we get `goodness = OK`.
- "Good" bit: `assert e` with e false irreversibly sets a bit to Fail; it does
  not get stuck. This lets verified code be linked with ill-typed adversaries
  that may get stuck, while distinguishing assertion failure from stuckness.
- Companion Theorem AdeqacySafety: a verified e, run from a good state, only
  reaches good states.
- Adversary interpretation: `lowval v := lift(lowloc) v` (Fig. 3). `lift Phi`
  lifts a location predicate to values: trivial on literals/unit, `Phi l` on
  locations, componentwise on pairs/sums, and for a function f (LiftRec)
  "`{lift Phi v} f v {y. lift Phi y}` as a NON-progressive triple" (guarded by
  later, because args may be built by untrusted code). `lowloc l` is persistent
  and gives no ownership; it is the only knowledge about low locations, and
  contents of a low location are always low (AllocLow/LoadLow/StoreLow).
  High locations (points-to) are private; HighNotLow: not both.
- Derived: LiftApp (lifted fun applied to lifted arg is stuck or lifted).

## 2. Cerise (Sec. 4.3, 5.1, 5.2)
- Adequacy (Thm 1): given memory invariant I over domain D within the program
  region, disjoint program and adversary memory fragments, adversary region
  holding no capabilities outside itself, registers = pc (rwx over prog) and r0
  (rwx cap over adv), rest integers, and an Iris proof of the initial
  configuration safe under I, then every reachable machine state satisfies I.
  Thm 5 (Sec. 7.4) is the version with malloc and an assert flag.
- Logical relation (Fig. 9, Sec. 5.1): unary, `V(w)` "safe to share" and
  `E(w)` "safe to execute", mutually defined via Iris guarded fixpoint (later).
  V: integers and opaque caps always; sentry caps if E of the encapsulated code
  (persistently); rw/rwx caps iff each cell of the range is in an invariant
  `exists w. a |-> w * V(w)`; ro/rx caps iff cells satisfy some persistent
  predicate that entails V. Non-trivial since points-to is not duplicable.
- FTLR (Thm 2): `V(perm,b,e,a) -> E(perm,b,e,a)` for arbitrary code behind the
  capability; this is the "universal contract" (Sec. 5.2). E is defined through
  the Cerise program logic's safe-execution triple.
- No runtime known/adversary distinction; it is purely logical.

## 3. Ideal signatures as ghost state (the Iris idiom)
OCPL Appendix B (Fig. 12) derives sign/verify from sealing, by specification:
- `MakeSignSpec`: precondition `persistent(P) and (forall v. P v -> lowval v)`;
  `makeseal ()` returns `(sign, verify)` with `exists gamma. issign gamma sign *
  isverify gamma verify`.
- `SignSpec`: `{issign g sign * P v} sign v {x. issigned g v x}`. So signing
  CONSUMES the abstract token `issign g sign` (the key) and `P v`.
- `VerifySpec`: `{isverify g verify * issigned g v v'} verify v' {ret v. P v}`;
  `VerifyAnySpec`: verify on any adversary value returns `P`-values or is stuck.
- `SignedLow`: `issigned g v x -> lowval x`; `VerifyLow`: verify is low;
  `SignedInv`: issigned implies P; `SignedAgree`: issigned determinism.
- Adversary gets no `issign` token: sign itself is NOT low, so never passed to
  untrusted code; verify and signatures are low, so freely shared.
Reading for plain Iris (the repo's setting), the standard realisation is: a
ghost-state resource indexed by key (`own gamma (excl ())` or an authoritative
map of signed messages) is the token; sign requires it; a persistent "signed
log" fragment is what verify checks. This realisation is OUR reading of the
idiom, not a statement quoted from either paper: UNVERIFIED against a source.
The pattern with `isseal/isunseal/issealed` as abstract predicates is what the
paper actually states; its Coq-level encoding of those predicates (ghost
resource choice) was NOT checked here (UNVERIFIED).

## UNVERIFIED / caveats
- Exact formula symbols and exact theorem hypotheses beyond the prose above.
- Cerise theorem numbers are from the arXiv/preprint layout; JACM numbering may
  differ. Cerise has no signature idiom; it is capability-machine specific.
- Whether the Coq proofs encode tokens as excl/auth ghost state: not checked.
