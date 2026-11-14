-- formal/lean4/FreedomKernel/Composition.lean
-- Veto-only composition: the verdict lattice of decision-os-min
-- (decision_os_min/compose.py: normalize, meet, compose) and the mint gate in
-- kernel.py decide(), where the authority verdict is folded with every
-- evaluator verdict by meet BEFORE any capability token is minted.
--
-- Gap: the Python defences that make evaluator output a bare verdict
-- (R1 sanitize, R2 canonical strings, R3 deep copy, I4 raise/timeout = DENY)
-- are assumed by the type `Raw`; they are tested, not proved, in decision-os-min.

namespace FreedomKernel.Composition

inductive Verdict | allow | limit | contain | defer | deny
  deriving DecidableEq, Repr

open Verdict

/-- compose.py `_RANK`: ALLOW ≺ LIMIT ≺ CONTAIN ≺ DEFER ≺ DENY. -/
def rank : Verdict → Nat
  | allow => 0 | limit => 1 | contain => 2 | defer => 3 | deny => 4

theorem rank_inj {a b : Verdict} (h : rank a = rank b) : a = b := by
  cases a <;> cases b <;> simp [rank] at h <;> rfl

theorem rank_le_four (a : Verdict) : rank a ≤ 4 := by cases a <;> simp [rank]

/-- Evaluator output as it reaches the fold. `none` is everything that is not a
lattice member: an off-lattice string, a dict without a verdict, a non-dict,
an exception, a timeout. compose.py `normalize`/`as_decision` and kernel.py's
I4 path send all of these to DENY. -/
abbrev Raw := Option Verdict

def normalize : Raw → Verdict
  | some v => v
  | none => deny

/-- compose.py `meet`: the more restrictive verdict. -/
def meet (a b : Verdict) : Verdict := if rank a ≥ rank b then a else b

/-- compose.py `PERMITTING = {ALLOW, LIMIT, CONTAIN}`: these mint a token. -/
def permitting (v : Verdict) : Bool := decide (rank v ≤ 2)

/-- The authority verdict folded with every evaluator verdict
(compose([authority] + evaluators); compose([]) = ALLOW and meet ALLOW a = a). -/
def composed (auth : Verdict) (evs : List Raw) : Verdict :=
  evs.foldl (fun acc e => meet acc (normalize e)) auth

/-- kernel.py: a token is minted only if the composed verdict is permitting. -/
def mintGate (auth : Verdict) (evs : List Raw) : Bool := permitting (composed auth evs)

-- ── Lattice laws ─────────────────────────────────────────────────────────────

theorem rank_meet (a b : Verdict) : rank (meet a b) = max (rank a) (rank b) := by
  unfold meet
  split <;> omega

theorem meet_comm (a b : Verdict) : meet a b = meet b a := by
  apply rank_inj; rw [rank_meet, rank_meet]; omega

theorem meet_assoc (a b c : Verdict) : meet (meet a b) c = meet a (meet b c) := by
  apply rank_inj; simp only [rank_meet]; omega

theorem meet_deny_left (a : Verdict) : meet deny a = deny := by
  apply rank_inj; rw [rank_meet]
  have h1 := rank_le_four a
  have h2 : rank deny = 4 := rfl
  omega

theorem meet_deny_right (a : Verdict) : meet a deny = deny := by
  rw [meet_comm]; exact meet_deny_left a

theorem meet_allow_left (a : Verdict) : meet allow a = a := by
  apply rank_inj; rw [rank_meet]; simp [rank]

-- ── The fold ─────────────────────────────────────────────────────────────────

private theorem fold_ge_acc (evs : List Raw) (acc : Verdict) :
    rank acc ≤ rank (evs.foldl (fun acc e => meet acc (normalize e)) acc) := by
  induction evs generalizing acc with
  | nil => simp
  | cons e es ih =>
    simp only [List.foldl]
    have := ih (meet acc (normalize e))
    rw [rank_meet] at this
    omega

private theorem fold_ge_mem (evs : List Raw) (acc : Verdict) (e : Raw) (he : e ∈ evs) :
    rank (normalize e) ≤ rank (evs.foldl (fun acc e => meet acc (normalize e)) acc) := by
  induction evs generalizing acc with
  | nil => cases he
  | cons x xs ih =>
    simp only [List.foldl]
    rcases List.mem_cons.mp he with h | h
    · subst h
      have := fold_ge_acc xs (meet acc (normalize e))
      rw [rank_meet] at this
      omega
    · exact ih _ h

/-- Evaluator order carries no meaning (compose.py: commutative/associative). -/
theorem composed_perm {evs evs' : List Raw} (a : Verdict) (h : evs.Perm evs') :
    composed a evs = composed a evs' := by
  unfold composed
  induction h generalizing a with
  | nil => rfl
  | cons x _ ih => exact ih _
  | swap x y l =>
    simp only [List.foldl]
    congr 1
    rw [meet_assoc, meet_assoc, meet_comm (normalize y)]
  | trans _ _ ih1 ih2 => exact (ih1 a).trans (ih2 a)

/-- Composition never loosens the authority ruling. -/
theorem composed_ge_authority (a : Verdict) (evs : List Raw) :
    rank a ≤ rank (composed a evs) := fold_ge_acc evs a

/-- Composition is at least as restrictive as every evaluator. -/
theorem composed_ge_each (a : Verdict) (evs : List Raw) (e : Raw) (he : e ∈ evs) :
    rank (normalize e) ≤ rank (composed a evs) := fold_ge_mem evs a e he

-- ── The security statements ──────────────────────────────────────────────────

/-- Non-amplification: a token is minted only if authority itself permits AND
every evaluator permits. No evaluator can create authority. -/
theorem non_amplification (a : Verdict) (evs : List Raw) (h : mintGate a evs = true) :
    permitting a = true ∧ ∀ e ∈ evs, permitting (normalize e) = true := by
  unfold mintGate permitting at *
  simp only [decide_eq_true_eq] at *
  refine ⟨Nat.le_trans (composed_ge_authority a evs) h, fun e he => ?_⟩
  exact Nat.le_trans (composed_ge_each a evs e he) h

/-- If authority does not permit, no set of evaluators can make it permit. -/
theorem authority_denial_final (a : Verdict) (evs : List Raw)
    (h : permitting a = false) : mintGate a evs = false := by
  cases hm : mintGate a evs
  · rfl
  · have := (non_amplification a evs hm).1; rw [h] at this; cases this

/-- Any single DENY vetoes (DENY is absorbing). -/
theorem veto_blocks (a : Verdict) (evs : List Raw) (e : Raw) (he : e ∈ evs)
    (hd : normalize e = deny) : mintGate a evs = false := by
  have := composed_ge_each a evs e he
  have h4 : rank (normalize e) = 4 := by rw [hd]; rfl
  unfold mintGate permitting
  simp only [decide_eq_false_iff_not]
  omega

/-- Malformed evaluator output fails closed. -/
theorem malformed_blocks (a : Verdict) (evs : List Raw) (h : none ∈ evs) :
    mintGate a evs = false := veto_blocks a evs none h rfl

/-- Adding an evaluator can only remove tokens, never add one. -/
theorem add_evaluator_restricts (a : Verdict) (evs : List Raw) (e : Raw)
    (h : mintGate a (evs ++ [e]) = true) : mintGate a evs = true := by
  unfold mintGate permitting composed at *
  simp only [decide_eq_true_eq, List.foldl_append, List.foldl] at *
  rw [rank_meet] at h
  omega

-- Non-claim (compose.py "Obligations"): LIMIT ∧ CONTAIN composes to CONTAIN,
-- so the redaction obligation of LIMIT is dropped. Obligation union is future work.
theorem limit_contain_drops_redaction : meet limit contain = contain := rfl

end FreedomKernel.Composition
