/-!
===============================================================================
ParticipationPath.lean
Agent-Level Participation Monotonicity in Multi-Basin Systems
===============================================================================

Author: Sean Timothy
Date: 2026-01-18

Purpose:
  Formalize a bias-neutral notion of a Participation Path:
  an agent in a multi-basin system can always choose a rule change
  that preserves participation monotonicity, unless the system
  degenerates to a single rule configuration.

Design Principles:
  • Single-agent reasoning
  • Participation as primary invariant
  • Rule changes as actions, not axioms
  • No basin internals required
  • Lean-clean (no admits, no classical reasoning)

===============================================================================
-/

universe u

/-- Abstract entities -/
constant Agent : Type u
constant Rule  : Type u
constant Basin : Type u

/-- Discrete time -/
abbrev Time := ℕ

/-- Participation capacity of an agent over time -/
constant Participation : Agent → Time → ℝ

/-- Rule-set used by an agent at a given time -/
constant RulesOf : Agent → Time → Rule

/-- A rule change is an action available to the agent -/
constant RuleChange : Agent → Time → Rule → Prop

/-
Rule change modes:
  symmetric   → increases shared structure (lasso / ride)
  asymmetric  → reduces shared structure (push off / escape)
-/
inductive RuleMode
| symmetric
| asymmetric

/-- Every rule change has a mode -/
constant RuleModeOf : Rule → Rule → RuleMode

/-
Participation dynamics assumptions:
  Rule changes preserve agent participation
  depending on their symmetry class.
-/
axiom symmetric_participation_non_decreasing :
  ∀ (a : Agent) (t : Time) (r r' : Rule),
    RulesOf a t = r →
    RuleModeOf r r' = RuleMode.symmetric →
    RuleChange a t r' →
    Participation a (t+1) ≥ Participation a t

axiom asymmetric_participation_non_decreasing :
  ∀ (a : Agent) (t : Time) (r r' : Rule),
    RulesOf a t = r →
    RuleModeOf r r' = RuleMode.asymmetric →
    RuleChange a t r' →
    Participation a (t+1) ≥ Participation a t

/-
Non-degeneracy assumption:
  The agent always has at least one alternative rule available.
  This excludes the single-basin collapse case.
-/
axiom non_degenerate_rules :
  ∀ (a : Agent) (t : Time),
    ∃ r' : Rule,
      r' ≠ RulesOf a t ∧ RuleChange a t r'

/-
Core Lemma:
  At any time step, the agent can choose a rule change
  that preserves participation monotonicity.
-/
theorem participation_step_exists :
  ∀ (a : Agent) (t : Time),
    ∃ r' : Rule,
      RuleChange a t r' ∧
      Participation a (t+1) ≥ Participation a t :=
by
  intro a t
  obtain ⟨r', hne, hchange⟩ := non_degenerate_rules a t
  let r := RulesOf a t
  cases hmode : RuleModeOf r r' with
  | symmetric =>
      refine ⟨r', hchange, ?_⟩
      exact symmetric_participation_non_decreasing
        a t r r' rfl hmode hchange
  | asymmetric =>
      refine ⟨r', hchange, ?_⟩
      exact asymmetric_participation_non_decreasing
        a t r r' rfl hmode hchange

/-- A Participation Path is a monotone participation trajectory -/
def ParticipationPath (a : Agent) : Prop :=
  ∀ t : Time,
    Participation a (t+1) ≥ Participation a t

/-
Main Theorem:
  Any agent in a non-degenerate multi-basin system
  admits a Participation Path.
-/
theorem agent_has_participation_path :
  ∀ a : Agent,
    ParticipationPath a :=
by
  intro a t
  obtain ⟨r', hchange, hmono⟩ := participation_step_exists a t
  exact hmono
