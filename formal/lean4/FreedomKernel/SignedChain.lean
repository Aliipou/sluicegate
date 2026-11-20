-- formal/lean4/FreedomKernel/SignedChain.lean
-- CRYPTO_VERIFICATION_PLAN.md §5: from "the verifier accepts a signed-token
-- chain" to "an abstract capability chain with the same or fewer rights".
--
-- SCOPE (read this): the theorem below is about the LEAN MODEL of the verifier
-- (Chain.walk with `sigOk` instantiated by `Ed25519.Verify`), NOT about the Rust
-- code in authgate-kernel/src/tcb/dag.rs. The Lean-to-Rust step is admitted.
-- It is also only relative to the axiom `ed25519_euf_cma` and carries that
-- axiom's hypotheses on every key in the walked chain:
--   * `¬SmallOrder pk`: corresponds to a Rust check that EXISTS on branch
--     t3-verify-strict (verify_strict at all 4 TCB sites; tests
--     tcb::dag::tests::root_small_order_key_rejected,
--     delegated_small_order_issuer_key_rejected and the engine/consent
--     equivalents; mutating to plain `verify` fails 8 tests). That is TESTED,
--     NOT PROVED: the Lean-to-Rust link is admitted.
--   * `¬Compromised pk`: remains a pure assumption (key custody).
-- The message encoding `enc` is a free parameter. The main theorem does not
-- need it injective (its conclusion is about the bytes `enc t`); the corollary
-- `signed_token_unique` adds an injectivity hypothesis on `enc` explicitly. No concrete
-- encoding is modelled, so injectivity and domain separation across the three
-- signed grammars (see Ed25519.lean item 5) are NOT proved here.
import Chain
import Ed25519

namespace FreedomKernel.SignedChain
open FreedomKernel.Chain FreedomKernel.Ed25519

/-- A signed token: the capability fields, the issuer key, and the signature. -/
structure Tok where
  epoch : Nat
  resource : Nat
  rights : BitVec 64
  isRoot : Bool
  bindsParent : Bool
  pk : PubKey
  sig : Sig

/-- The node the verifier sees: `sigOk` is the checker's verdict on `enc t`,
    the bytes the token claims to have been signed over. -/
def Tok.toNode (enc : Tok → Msg) (t : Tok) : Node :=
  { epoch := t.epoch, resource := t.resource, rights := t.rights,
    isRoot := t.isRoot, sigOk := Verify t.pk (enc t) t.sig, bindsParent := t.bindsParent }

/-- The signature-free abstract capability node: same fields, `sigOk` granted. -/
def Tok.toAbs (t : Tok) : Node :=
  { epoch := t.epoch, resource := t.resource, rights := t.rights,
    isRoot := t.isRoot, sigOk := true, bindsParent := t.bindsParent }

/-- Model of the verifier on a signed chain (leaf first). -/
def verify (enc : Tok → Msg) (m : Nat) (toks : List Tok) : Option (Node × Nat) :=
  walk m 0 (toks.map (Tok.toNode enc))

/-- Abstract capability chain: the same walk with the signature check granted
    (what Chain.lean's rights/resource/epoch logic alone requires). -/
def absChain (m : Nat) (toks : List Tok) : Option (Node × Nat) :=
  walk m 0 (toks.map Tok.toAbs)

/-- Every node in the walked prefix (leaf .. root, h+1 nodes) passed `sigOk`. -/
theorem walk_sigs (m : Nat) : ∀ (chain : List Node) (d : Nat) (r : Node) (h : Nat),
    walk m d chain = some (r, h) → ∀ n ∈ chain.take (h + 1), n.sigOk = true := by
  intro chain
  induction chain with
  | nil => intro d r h hw; simp [walk] at hw
  | cons n rest ih =>
    intro d r h hw
    unfold walk at hw
    split at hw; · simp at hw
    split at hw; · simp at hw
    split at hw; · simp at hw
    rename_i hd he hs
    have hs' : n.sigOk = true := by simpa using hs
    split at hw
    · simp only [Option.some.injEq, Prod.mk.injEq] at hw
      obtain ⟨_, rfl⟩ := hw
      intro x hx
      simp at hx
      subst hx; exact hs'
    · split at hw
      · simp at hw
      · rename_i p ps
        split at hw; · simp at hw
        split at hw; · simp at hw
        split at hw; · simp at hw
        cases hrec : walk m (d + 1) (p :: ps) with
        | none => rw [hrec] at hw; simp at hw
        | some rh =>
          rw [hrec] at hw
          simp only [Option.map_some', Option.some.injEq, Prod.mk.injEq] at hw
          obtain ⟨_, rfl⟩ := hw
          intro x hx
          have hx' : x ∈ n :: (p :: ps).take (rh.2 + 1) := by
            simpa [List.take_succ_cons] using hx
          rcases List.mem_cons.mp hx' with rfl | hx2
          · exact hs'
          · exact ih (d + 1) rh.1 rh.2 hrec x hx2

/-- Grant the signature check on a node. -/
def absN (n : Node) : Node := { n with sigOk := true }

/-- Granting every signature check cannot make an accepted walk fail: the
    abstract chain accepts with the same hop count and the root with the same
    resource and rights. -/
theorem walk_absN (m : Nat) : ∀ (chain : List Node) (d : Nat) (r : Node) (h : Nat),
    walk m d chain = some (r, h) → walk m d (chain.map absN) = some (absN r, h) := by
  intro chain
  induction chain with
  | nil => intro d r h hw; simp [walk] at hw
  | cons n rest ih =>
    intro d r h hw
    unfold walk at hw
    split at hw; · simp at hw
    split at hw; · simp at hw
    split at hw; · simp at hw
    rename_i hd he hs
    split at hw
    · rename_i hroot
      simp only [Option.some.injEq, Prod.mk.injEq] at hw
      obtain ⟨rfl, rfl⟩ := hw
      simp [walk, absN, hd, he, hroot]
    · rename_i hroot
      split at hw
      · simp at hw
      · rename_i p ps
        split at hw; · simp at hw
        split at hw; · simp at hw
        split at hw; · simp at hw
        rename_i hres hb hr
        cases hrec : walk m (d + 1) (p :: ps) with
        | none => rw [hrec] at hw; simp at hw
        | some rh =>
          rw [hrec] at hw
          simp only [Option.map_some', Option.some.injEq, Prod.mk.injEq] at hw
          obtain ⟨rfl, rfl⟩ := hw
          have := ih (d + 1) rh.1 rh.2 hrec
          simp only [List.map_cons] at this ⊢
          unfold walk
          simp [absN, hd, he, hroot, hres, hb, hr]
          exact ⟨Classical.not_not.mp hr, by simpa [absN] using this⟩

theorem walk_abs (m : Nat) (chain : List Tok) (d : Nat) (r : Node) (h : Nat)
    (enc : Tok → Msg)
    (hw : walk m d (chain.map (Tok.toNode enc)) = some (r, h)) :
    walk m d (chain.map Tok.toAbs) = some (absN r, h) := by
  have e : chain.map Tok.toAbs = (chain.map (Tok.toNode enc)).map absN := by
    rw [List.map_map]; apply List.map_congr_left; intro a _; rfl
  rw [e]; exact walk_absN m _ d r h hw

/-- **PROVED relative to `ed25519_euf_cma`, model level.**
    If the Lean model of the verifier accepts a signed-token chain
    (reaching root `r` after `h` hops), then
    (1) every token in the walked prefix was honestly signed over its encoded
        bytes (`Signed pk (enc t)`), given the EUF-CMA hypotheses on its key;
    (2) the abstract (signature-free) capability chain accepts the same tokens
        with the same hop count and the same root resource and rights; and
    (3) the leaf's rights are a subset of the root's (`NoExcess`), on one
        resource, within `MAX_CHAIN_DEPTH` hops. -/
theorem signed_chain_implies_abstract_chain
    (enc : Tok → Msg) (m : Nat) (leaf : Tok) (rest : List Tok) (r : Node) (h : Nat)
    (hkeys : ∀ t ∈ (leaf :: rest).take (h + 1), ¬ SmallOrder t.pk ∧ ¬ Compromised t.pk)
    (hacc : verify enc m (leaf :: rest) = some (r, h)) :
    (∀ t ∈ (leaf :: rest).take (h + 1), Signed t.pk (enc t)) ∧
    (∃ a, absChain m (leaf :: rest) = some (a, h) ∧
          a.rights = r.rights ∧ a.resource = r.resource ∧ a.isRoot = true) ∧
    NoExcess leaf.rights r.rights ∧ leaf.resource = r.resource ∧ h ≤ MAX_CHAIN_DEPTH := by
  unfold verify at hacc
  obtain ⟨hroot, hex, hres, _, _, hdep⟩ :=
    walk_sound m ((leaf :: rest).map (Tok.toNode enc)) 0 (Tok.toNode enc leaf) r h rfl hacc
  refine ⟨?_, ⟨absN r, walk_abs m (leaf :: rest) 0 r h enc hacc, rfl, rfl, hroot⟩,
    hex, hres, by omega⟩
  intro t ht
  have hs := walk_sigs m _ 0 r h hacc (Tok.toNode enc t)
    (by
      have : ((leaf :: rest).map (Tok.toNode enc)).take (h + 1)
          = ((leaf :: rest).take (h + 1)).map (Tok.toNode enc) := by
        rw [List.map_take]
      rw [this]; exact List.mem_map_of_mem _ ht)
  exact ed25519_euf_cma t.pk (enc t) t.sig (hkeys t ht).1 (hkeys t ht).2 hs

/-- With an explicitly assumed injective encoding, a signed message pins down
    the token: any token encoding to the same bytes as a walked token IS it.
    `hinj` is a HYPOTHESIS, not something this development proves. -/
theorem signed_token_unique (enc : Tok → Msg) (hinj : ∀ a b, enc a = enc b → a = b)
    (t t' : Tok) (h : enc t' = enc t) : t' = t := hinj _ _ h

-- Expected: depends on [FreedomKernel.Ed25519.ed25519_euf_cma] (plus Lean's own).
#print axioms signed_chain_implies_abstract_chain

end FreedomKernel.SignedChain
