-- formal/lean4/FreedomKernel/MultiAgent.lean
-- Multi-agent attenuation theorem: child authority ⊆ parent authority.
-- Mirrors multi_agent.rs structural constraint.

namespace FreedomKernel.MultiAgent

-- ── Authority as a set of resource permissions ────────────────────────────────

structure Permission where
  resourceId : String
  canRead    : Bool
  canWrite   : Bool
  canDelegate: Bool
  deriving DecidableEq, Repr

abbrev Authority := List Permission

-- ── Attenuation ───────────────────────────────────────────────────────────────

-- Child authority is attenuated: every child permission is covered by a parent
-- permission ON THE SAME RESOURCE with at least the same rights.
-- (The earlier form `resourceId = … → rights` was vacuous: any child permission
-- was "covered" by a parent permission on a different resource.)
--
-- Gap: this is the specification. multi_agent.rs `verify_spawn` does not read
-- `delegated_claims`; rights narrowing is enforced in tcb/dag.rs, see Chain.lean.

def permissionSubset (child parent : Permission) : Prop :=
  child.resourceId = parent.resourceId ∧
  (child.canRead = true → parent.canRead = true) ∧
  (child.canWrite = true → parent.canWrite = true) ∧
  (child.canDelegate = true → parent.canDelegate = true)

def authorityAttenuated (child parent : Authority) : Prop :=
  ∀ cp ∈ child, ∃ pp ∈ parent, permissionSubset cp pp

theorem permissionSubset_refl (p : Permission) : permissionSubset p p :=
  ⟨rfl, id, id, id⟩

theorem permissionSubset_trans {a b c : Permission}
    (h1 : permissionSubset a b) (h2 : permissionSubset b c) : permissionSubset a c :=
  ⟨h1.1.trans h2.1, fun h => h2.2.1 (h1.2.1 h), fun h => h2.2.2.1 (h1.2.2.1 h),
    fun h => h2.2.2.2 (h1.2.2.2 h)⟩

theorem attenuated_refl (A : Authority) : authorityAttenuated A A :=
  fun cp h => ⟨cp, h, permissionSubset_refl cp⟩

/-- Attenuation composes along a delegation chain. -/
theorem attenuated_trans {C B A : Authority}
    (h1 : authorityAttenuated C B) (h2 : authorityAttenuated B A) : authorityAttenuated C A := by
  intro cp hc
  obtain ⟨bp, hb, hcb⟩ := h1 cp hc
  obtain ⟨ap, ha, hba⟩ := h2 bp hb
  exact ⟨ap, ha, permissionSubset_trans hcb hba⟩

theorem no_read_escalation {child parent : Authority} (h : authorityAttenuated child parent)
    {cp : Permission} (hc : cp ∈ child) (hr : cp.canRead = true) :
    ∃ pp ∈ parent, pp.resourceId = cp.resourceId ∧ pp.canRead = true := by
  obtain ⟨pp, hp, hs⟩ := h cp hc
  exact ⟨pp, hp, hs.1.symm, hs.2.1 hr⟩

theorem no_write_escalation {child parent : Authority} (h : authorityAttenuated child parent)
    {cp : Permission} (hc : cp ∈ child) (hw : cp.canWrite = true) :
    ∃ pp ∈ parent, pp.resourceId = cp.resourceId ∧ pp.canWrite = true := by
  obtain ⟨pp, hp, hs⟩ := h cp hc
  exact ⟨pp, hp, hs.1.symm, hs.2.2.1 hw⟩

theorem no_delegate_escalation {child parent : Authority} (h : authorityAttenuated child parent)
    {cp : Permission} (hc : cp ∈ child) (hd : cp.canDelegate = true) :
    ∃ pp ∈ parent, pp.resourceId = cp.resourceId ∧ pp.canDelegate = true := by
  obtain ⟨pp, hp, hs⟩ := h cp hc
  exact ⟨pp, hp, hs.1.symm, hs.2.2.2 hd⟩

/-- Nothing can be delegated from an empty authority. -/
theorem attenuated_nil {child : Authority} (h : authorityAttenuated child []) : child = [] := by
  cases child with
  | nil => rfl
  | cons cp _ =>
    obtain ⟨_, hp, _⟩ := h cp (List.mem_cons_self _ _)
    cases hp

-- ── Depth cap ────────────────────────────────────────────────────────────────

-- multi_agent.rs MAX_DELEGATION_DEPTH and `AuthorityBudget::with_depth`, which
-- clamps the requested depth. The chain-walk bound is `Chain.walk_hops`.
def MAX_DELEGATION_DEPTH : Nat := 16

def withDepth (d : Nat) : Nat := min d MAX_DELEGATION_DEPTH

theorem withDepth_le (d : Nat) : withDepth d ≤ MAX_DELEGATION_DEPTH := Nat.min_le_right _ _

end FreedomKernel.MultiAgent
