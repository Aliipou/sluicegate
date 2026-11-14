-- formal/lean4/FreedomKernel/TCB.lean
-- Formal theorems about Freedom Kernel TCB properties.
-- Mirrors engine.rs types and invariants.
--
-- Build: cd formal/lean4/FreedomKernel && lake build
-- Status: every theorem in this file builds with zero `sorry` (fixed
-- 2026-09-16: permitted_implies_no_forbidden_flag used a removed Lean4 core
-- lemma name; see DECISIONS.md). See FreedomKernel/Incompleteness.lean for
-- what this file does NOT claim (semantic intent, axiom soundness).

namespace FreedomKernel

-- ── Core types ───────────────────────────────────────────────────────────────

inductive AgentType | Human | Machine
  deriving DecidableEq, Repr

structure Entity where
  id : String
  agentType : AgentType
  deriving Repr

structure Resource where
  id : String
  scope : String
  deriving Repr

structure RightsClaim where
  entity : Entity
  resource : Resource
  canRead : Bool
  canWrite : Bool
  canDelegate : Bool
  deriving Repr

-- ── ActionIR ─────────────────────────────────────────────────────────────────
-- Only the fields relevant to the 10 forbidden flags and axiom checks.

structure ActionIR where
  id : String
  actor : Entity
  increasesMachineSovereignty : Bool := false
  resistsHumanCorrection      : Bool := false
  bypassesVerifier            : Bool := false
  weakensVerifier             : Bool := false
  disablesCorrigibility       : Bool := false
  machineCoalitionDominion    : Bool := false
  coerces                     : Bool := false
  deceives                    : Bool := false
  selfModificationWeakens     : Bool := false
  machineCoalitionReduces     : Bool := false
  governsHumans               : List Entity := []
  deriving Repr

-- ── hasForbiddenFlag ─────────────────────────────────────────────────────────

def hasForbiddenFlag (a : ActionIR) : Bool :=
  a.increasesMachineSovereignty ||
  a.resistsHumanCorrection      ||
  a.bypassesVerifier            ||
  a.weakensVerifier             ||
  a.disablesCorrigibility       ||
  a.machineCoalitionDominion    ||
  a.coerces                     ||
  a.deceives                    ||
  a.selfModificationWeakens     ||
  a.machineCoalitionReduces

-- ── Verification result ───────────────────────────────────────────────────────

inductive Outcome | Permitted | Blocked
  deriving DecidableEq, Repr

-- ── verify (simplified model — flag check only) ───────────────────────────────
-- Full verify also checks A4/A6/A7. Those are proved in separate lemmas below.
-- This definition captures the forbidden-flag layer unconditionally.

def verifyFlags (a : ActionIR) : Outcome :=
  if hasForbiddenFlag a then .Blocked else .Permitted

-- ── P1: Forbidden flags always block ────────────────────────────────────────

-- PROOF: unconditional — follows directly from definition of verifyFlags and hasForbiddenFlag.
theorem forbidden_flags_always_block (a : ActionIR) (h : hasForbiddenFlag a = true) :
    verifyFlags a = .Blocked := by
  simp [verifyFlags, h]

-- Individual flag corollaries

theorem sovereignty_flag_blocks (a : ActionIR) (h : a.increasesMachineSovereignty = true) :
    verifyFlags a = .Blocked := by
  apply forbidden_flags_always_block
  simp [hasForbiddenFlag, h]

theorem coercion_flag_blocks (a : ActionIR) (h : a.coerces = true) :
    verifyFlags a = .Blocked := by
  apply forbidden_flags_always_block
  simp [hasForbiddenFlag, h]

theorem deception_flag_blocks (a : ActionIR) (h : a.deceives = true) :
    verifyFlags a = .Blocked := by
  apply forbidden_flags_always_block
  simp [hasForbiddenFlag, h]

-- P5 (determinism) is not stated here: every Lean function is deterministic,
-- so `verifyFlags a = verifyFlags a` said nothing. Determinism of the Rust
-- engine is the Kani harness `prop_permitted_deterministic`.

-- ── P2: If permitted, no forbidden flag is set ────────────────────────────────

theorem permitted_implies_no_forbidden_flag (a : ActionIR) (h : verifyFlags a = .Permitted) :
    hasForbiddenFlag a = false := by
  unfold verifyFlags at h
  cases hf : hasForbiddenFlag a with
  | true => simp [hf] at h
  | false => rfl

-- ── A4: Ownerless machine model ────────────────────────────────────────────────

structure OwnershipGraph where
  machineOwners : List (Entity × Entity)  -- (machine, owner)

def hasOwner (g : OwnershipGraph) (e : Entity) : Bool :=
  g.machineOwners.any (fun (m, _) => m.id == e.id)

-- ── verifyCore: forbidden flags + A4 + A6 (engine.rs `verify`, steps 1-3) ──
-- Gap: resource access checks (engine.rs step 4, `can_act`) are not modelled;
-- engine.rs matches owners by name, this model by `Entity.id`.

def isMachine (e : Entity) : Bool := decide (e.agentType = AgentType.Machine)

def a4Violation (g : OwnershipGraph) (a : ActionIR) : Bool :=
  isMachine a.actor && !hasOwner g a.actor

def a6Violation (a : ActionIR) : Bool :=
  isMachine a.actor && !a.governsHumans.isEmpty

def verifyCore (g : OwnershipGraph) (a : ActionIR) : Outcome :=
  if hasForbiddenFlag a || a4Violation g a || a6Violation a then .Blocked else .Permitted

/-- A4: a machine with no registered owner is blocked. -/
theorem ownerless_machine_blocked (g : OwnershipGraph) (a : ActionIR)
    (hm : a.actor.agentType = AgentType.Machine) (hno : hasOwner g a.actor = false) :
    verifyCore g a = .Blocked := by
  simp [verifyCore, a4Violation, isMachine, hm, hno]

/-- A6: a machine that governs any human is blocked. -/
theorem machine_cannot_govern_human (g : OwnershipGraph) (a : ActionIR) (h : Entity)
    (hm : a.actor.agentType = AgentType.Machine) (hh : h ∈ a.governsHumans) :
    verifyCore g a = .Blocked := by
  have hne : a.governsHumans.isEmpty = false := by
    cases hg : a.governsHumans with
    | nil => rw [hg] at hh; cases hh
    | cons _ _ => rfl
  simp [verifyCore, a6Violation, isMachine, hm, hne]

/-- Exactly what a Permitted verdict guarantees. -/
theorem verifyCore_permitted_iff (g : OwnershipGraph) (a : ActionIR) :
    verifyCore g a = .Permitted ↔
      hasForbiddenFlag a = false ∧
      (a.actor.agentType = AgentType.Machine → hasOwner g a.actor = true) ∧
      (a.actor.agentType = AgentType.Machine → a.governsHumans = []) := by
  unfold verifyCore a4Violation a6Violation isMachine
  cases hf : hasForbiddenFlag a <;> cases ht : a.actor.agentType <;>
    cases ho : hasOwner g a.actor <;> cases hg : a.governsHumans <;> simp_all

/-- The core verdict refines the flag-only verdict. -/
theorem verifyCore_permitted_implies_flags (g : OwnershipGraph) (a : ActionIR)
    (h : verifyCore g a = .Permitted) : verifyFlags a = .Permitted := by
  have := ((verifyCore_permitted_iff g a).mp h).1
  simp [verifyFlags, this]

end FreedomKernel
