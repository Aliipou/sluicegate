-- formal/lean4/FreedomKernel/Chain.lean
-- Delegation-chain validation: model of authgate-kernel/src/tcb/dag.rs
-- `validate_chain`, without cryptography.
--
-- Gap: Ed25519 verification and the SHA-256 issuer binding (AT-5.1) are
-- abstracted as the Bools `sigOk` and `bindsParent`; the Rust walk finds each
-- parent by hash in the bundle, here the list IS that walk (leaf first).

namespace FreedomKernel.Chain

/-- `(c &&& ~~~p) = 0`: no bit of `c` outside `p` (dag.rs attenuation check). -/
def NoExcess (c p : BitVec 64) : Prop := (c &&& ~~~p) = 0

theorem noExcess_bits {c p : BitVec 64} (h : NoExcess c p) (i : Nat) (hi : i < 64)
    (hc : c.getLsbD i = true) : p.getLsbD i = true := by
  have := congrArg (fun x => x.getLsbD i) h
  simp only [BitVec.getLsbD_and, BitVec.getLsbD_not, BitVec.getLsbD_zero, hc, hi,
    decide_True, Bool.true_and] at this
  cases hp : p.getLsbD i <;> simp_all

theorem noExcess_of_bits {c p : BitVec 64}
    (h : ∀ i, i < 64 → c.getLsbD i = true → p.getLsbD i = true) : NoExcess c p := by
  unfold NoExcess
  apply BitVec.eq_of_getLsbD_eq
  intro ⟨i, hi⟩
  simp only [BitVec.getLsbD_and, BitVec.getLsbD_not, BitVec.getLsbD_zero, hi, decide_True,
    Bool.true_and]
  cases hc : c.getLsbD i
  · simp
  · simp [h i hi hc]

theorem noExcess_refl (c : BitVec 64) : NoExcess c c :=
  noExcess_of_bits fun _ _ h => h

/-- Attenuation composes along a chain. -/
theorem noExcess_trans {c b a : BitVec 64} (h1 : NoExcess c b) (h2 : NoExcess b a) :
    NoExcess c a :=
  noExcess_of_bits fun i hi hc => noExcess_bits h2 i hi (noExcess_bits h1 i hi hc)

structure Node where
  epoch : Nat
  resource : Nat
  rights : BitVec 64
  isRoot : Bool
  sigOk : Bool
  bindsParent : Bool

def MAX_CHAIN_DEPTH : Nat := 16

/-- dag.rs `validate_chain`; returns the root reached and the number of hops. -/
def walk (m : Nat) : Nat → List Node → Option (Node × Nat)
  | _, [] => none
  | d, n :: rest =>
    if d > MAX_CHAIN_DEPTH then none
    else if n.epoch < m then none
    else if n.sigOk = false then none
    else if n.isRoot = true then some (n, 0)
    else match rest with
      | [] => none
      | p :: _ =>
        if n.resource ≠ p.resource then none
        else if n.bindsParent = false then none
        else if (n.rights &&& ~~~p.rights) ≠ 0 then none
        else (walk m (d + 1) rest).map (fun rh => (rh.1, rh.2 + 1))

/-- Everything an accepted walk guarantees about its leaf and root. -/
theorem walk_sound (m : Nat) : ∀ (chain : List Node) (d : Nat) (leaf : Node)
    (r : Node) (h : Nat), chain.head? = some leaf → walk m d chain = some (r, h) →
    r.isRoot = true ∧ NoExcess leaf.rights r.rights ∧ leaf.resource = r.resource ∧
    m ≤ leaf.epoch ∧ m ≤ r.epoch ∧ d + h ≤ MAX_CHAIN_DEPTH := by
  intro chain
  induction chain with
  | nil => intro d leaf r h hh; simp at hh
  | cons n rest ih =>
    intro d leaf r h hh hw
    simp only [List.head?, Option.some.injEq] at hh
    subst hh
    unfold walk at hw
    split at hw; · simp at hw
    split at hw; · simp at hw
    split at hw; · simp at hw
    rename_i hd he hs
    split at hw
    · rename_i hroot
      simp only [Option.some.injEq, Prod.mk.injEq] at hw
      obtain ⟨rfl, rfl⟩ := hw
      refine ⟨hroot, noExcess_refl _, rfl, by omega, by omega, by omega⟩
    · split at hw
      · simp at hw
      · rename_i p ps
        split at hw; · simp at hw
        split at hw; · simp at hw
        split at hw; · simp at hw
        rename_i hres _ hrights
        cases hrec : walk m (d + 1) (p :: ps) with
        | none => rw [hrec] at hw; simp at hw
        | some rh =>
          rw [hrec] at hw
          simp only [Option.map_some', Option.some.injEq, Prod.mk.injEq] at hw
          obtain ⟨rfl, rfl⟩ := hw
          obtain ⟨hr, hex, hresr, hep, hepr, hdep⟩ := ih (d + 1) p rh.1 rh.2 rfl hrec
          have hstep : NoExcess n.rights p.rights := by
            unfold NoExcess; exact Classical.not_not.mp hrights
          refine ⟨hr, noExcess_trans hstep hex, ?_, by omega, hepr, by omega⟩
          exact (Classical.not_not.mp hres).trans hresr

/-- From the leaf (d = 0): at most 16 hops, i.e. 17 nodes. -/
theorem walk_hops (m : Nat) (n : Node) (rest : List Node) (r : Node) (h : Nat)
    (hw : walk m 0 (n :: rest) = some (r, h)) : h ≤ MAX_CHAIN_DEPTH := by
  have := (walk_sound m (n :: rest) 0 n r h rfl hw).2.2.2.2.2
  omega

/-- The leaf's rights never exceed the root grant's rights. -/
theorem walk_rights (m : Nat) (n : Node) (rest : List Node) (r : Node) (h : Nat)
    (hw : walk m 0 (n :: rest) = some (r, h)) : NoExcess n.rights r.rights :=
  (walk_sound m (n :: rest) 0 n r h rfl hw).2.1

end FreedomKernel.Chain
