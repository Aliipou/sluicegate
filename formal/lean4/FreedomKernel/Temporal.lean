-- formal/lean4/FreedomKernel/Temporal.lean
-- Temporal IFC invariants: taint propagation across plan prefixes.
-- Mirrors planner.rs StateProjection logic.

namespace FreedomKernel.Temporal

-- ── Label lattice ─────────────────────────────────────────────────────────────

inductive Label | Public | Internal | Secret
  deriving DecidableEq, Repr

def labelRank : Label → Nat
  | .Public   => 0
  | .Internal => 1
  | .Secret   => 2

def labelDominates (a b : Label) : Bool :=
  labelRank a > labelRank b

-- ── Taint monotonicity ────────────────────────────────────────────────────────

def highest (a b : Label) : Label :=
  if labelRank a >= labelRank b then a else b

-- PROOF: taint can only increase across a plan prefix
theorem taint_monotone (current new_read : Label) :
    labelRank (highest current new_read) ≥ labelRank current := by
  unfold highest
  split <;> omega

-- ── planner.rs model: String labels, exactly as Rust ─────────────────────────
-- Mirrors `label_rank`, `highest_label`, `StateProjection::advance` and the IFC
-- part of `verify_plan`. Gap: the per-action kernel gate (engine::verify) that
-- verify_plan also runs is not modelled here (see TCB.lean `verifyCore`).

def labelRankS (s : String) : Nat :=
  if s = "SECRET" then 2 else if s = "INTERNAL" then 1 else 0

def highestS (cur : String) (ls : List String) : String :=
  ls.foldl (fun b l => if labelRankS l > labelRankS b then l else b) cur

theorem highestS_ge_cur (cur : String) (ls : List String) :
    labelRankS cur ≤ labelRankS (highestS cur ls) := by
  induction ls generalizing cur with
  | nil => simp [highestS]
  | cons l ls ih =>
    unfold highestS at *
    simp only [List.foldl]
    by_cases hlt : labelRankS l > labelRankS cur
    · have := ih l; rw [if_pos hlt]; omega
    · have := ih cur; rw [if_neg hlt]; omega

theorem highestS_ge_mem (cur : String) (ls : List String) (x : String) (hx : x ∈ ls) :
    labelRankS x ≤ labelRankS (highestS cur ls) := by
  induction ls generalizing cur with
  | nil => cases hx
  | cons l ls ih =>
    unfold highestS at *
    simp only [List.foldl]
    rcases List.mem_cons.mp hx with h | h
    · subst h
      by_cases hlt : labelRankS x > labelRankS cur
      · have := highestS_ge_cur x ls; unfold highestS at this; rw [if_pos hlt]; omega
      · have := highestS_ge_cur cur ls; unfold highestS at this; rw [if_neg hlt]; omega
    · exact ih _ h

/-- StateProjection::advance: empty labels are skipped on both sides. -/
def advance (t : String) (reads writes : List String) : Option String :=
  if writes.any (fun w => w != "" &&
      decide (labelRankS (highestS t (reads.filter (fun r => r != ""))) > labelRankS w))
  then none
  else some (highestS t (reads.filter (fun r => r != "")))

def verifyPlan : String → List (List String × List String) → Option String
  | t, [] => some t
  | t, (r, w) :: ss =>
    match advance t r w with
    | none => none
    | some t' => verifyPlan t' ss

theorem advance_monotone {t t' : String} {r w : List String}
    (h : advance t r w = some t') : labelRankS t ≤ labelRankS t' := by
  unfold advance at h
  split at h
  · cases h
  · cases h; exact highestS_ge_cur _ _

theorem advance_covers_reads {t t' x : String} {r w : List String}
    (h : advance t r w = some t') (hx : x ∈ r) (hne : x ≠ "") :
    labelRankS x ≤ labelRankS t' := by
  unfold advance at h
  split at h
  · cases h
  · cases h
    exact highestS_ge_mem _ _ _ (List.mem_filter.mpr ⟨hx, by simp [hne]⟩)

/-- No write lands below the taint accumulated so far. -/
theorem advance_no_downward_write {t t' y : String} {r w : List String}
    (h : advance t r w = some t') (hy : y ∈ w) (hne : y ≠ "") :
    labelRankS t' ≤ labelRankS y := by
  unfold advance at h
  split at h
  · cases h
  · rename_i hc
    cases h
    simp only [List.any_eq_true, not_exists, not_and] at hc
    have := hc y hy
    simp [hne] at this
    omega

theorem verifyPlan_append (t : String) (pre post : List (List String × List String))
    (tf : String) (h : verifyPlan t (pre ++ post) = some tf) :
    ∃ tm, verifyPlan t pre = some tm ∧ verifyPlan tm post = some tf := by
  induction pre generalizing t with
  | nil => exact ⟨t, rfl, h⟩
  | cons s ss ih =>
    obtain ⟨r, w⟩ := s
    simp only [List.cons_append, verifyPlan] at h ⊢
    cases ha : advance t r w with
    | none => rw [ha] at h; cases h
    | some t' => rw [ha] at h; simpa using ih t' h

theorem plan_writes_above_start (t tf : String) (ss : List (List String × List String))
    (h : verifyPlan t ss = some tf) :
    ∀ s ∈ ss, ∀ y ∈ s.2, y ≠ "" → labelRankS t ≤ labelRankS y := by
  induction ss generalizing t with
  | nil => intro s hs; cases hs
  | cons s ss ih =>
    obtain ⟨r, w⟩ := s
    simp only [verifyPlan] at h
    cases ha : advance t r w with
    | none => rw [ha] at h; cases h
    | some t' =>
      rw [ha] at h
      intro s' hs' y hy hne
      have hmono := advance_monotone ha
      rcases List.mem_cons.mp hs' with e | e
      · subst e
        have := advance_no_downward_write ha hy hne
        omega
      · have := ih t' h s' e y hy hne
        omega

/-- IFC over a whole plan: data read at step i is never written, at step i or
any later step, to a resource labelled below it. -/
theorem plan_no_downflow (t tf : String) (pre post : List (List String × List String))
    (r w : List String) (h : verifyPlan t (pre ++ (r, w) :: post) = some tf)
    (x : String) (hx : x ∈ r) (hxne : x ≠ "")
    (y : String) (hy : y ∈ w ∨ ∃ s ∈ post, y ∈ s.2) (hyne : y ≠ "") :
    labelRankS x ≤ labelRankS y := by
  obtain ⟨tm, _, hrest⟩ := verifyPlan_append t pre ((r, w) :: post) tf h
  simp only [verifyPlan] at hrest
  cases ha : advance tm r w with
  | none => rw [ha] at hrest; cases hrest
  | some t' =>
    rw [ha] at hrest
    have hread := advance_covers_reads ha hx hxne
    rcases hy with hy | ⟨s, hs, hy⟩
    · have := advance_no_downward_write ha hy hyne; omega
    · have := plan_writes_above_start t' tf post hrest s hs y hy hyne; omega

/-- NON-GUARANTEE (records a fail-open in planner.rs): an unknown label ranks as
PUBLIC, so reading "CONFIDENTIAL" data adds no taint and a later PUBLIC write
is allowed. Flip this when label_rank fails closed. -/
theorem unknown_label_fails_open :
    verifyPlan "PUBLIC" [(["CONFIDENTIAL"], []), ([], ["PUBLIC"])] = some "PUBLIC" := by
  decide

end FreedomKernel.Temporal
