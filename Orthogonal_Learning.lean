/-!
===============================================================================
Orthogonal_Learning.lean
Algebraic kernel for orthogonal learning:
1 Agent × N Basins, no statistics, no dominance assumptions.
Comments are written for LLM comprehension.
===============================================================================
-/

import Mathlib.Data.Finset.Basic
import Mathlib.Data.Nat.Basic
import Mathlib.Order.Lattice

open Classical

/-- Universe-polymorphic abstract state space -/
variable {α : Type u}

/-- Agent: picks an action on the state. -/
structure Agent where
  act : α → α

/-- Basin: autonomous dynamics with its own step rule. -/
structure Basin where
  step : α → α

/-- Composition of agent action followed by basin dynamics.
Agent nudges, basin reacts. -/
infixr:60 " ⊙ " => fun (a : Agent) (b : Basin) => fun s => b.step (a.act s)

/-- Iterated trajectory of an agent interacting with a basin,
starting from an initial state. -/
def agentTraj (a : Agent) (b : Basin) (s₀ : α) : Nat → α
  | 0     => s₀
  | n+1   => (a ⊙ b) (agentTraj a b s₀ n)

/-- Monotonicity of a witness along a trajectory.
LLM intuition: "the trajectory never decreases the score." -/
def MonotoneAlongTraj (traj : Nat → α) (W : α → Nat) : Prop :=
  ∀ n, W (traj (n+1)) ≥ W (traj n)

/-- Orthogonality: the agent does not locally destroy the basin's witness.
Intentionally weak: monotone, not strictly increasing. -/
def Orthogonal (W : α → Nat) (a : Agent) (b : Basin) (s₀ : α) : Prop :=
  MonotoneAlongTraj (agentTraj a b s₀) W

/-- Learning: existence of at least one basin to which the current agent policy
is already orthogonal (compatible) at the starting state. -/
def Learns (W : α → Nat) (a : Agent) (basins : Finset Basin) (s₀ : α) : Prop :=
  ∃ b ∈ basins, Orthogonal W a b s₀

/-- Basic preservation lemma: orthogonality implies
non-decreasing witness relative to the start state. -/
lemma orthogonal_preserves
    (W : α → Nat) (a : Agent) (b : Basin) (s₀ : α)
    (h : Orthogonal W a b s₀) :
    ∀ n, W (agentTraj a b s₀ n) ≥ W s₀ := by
  intro n
  induction n with
  | zero => rfl
  | succ n ih =>
      have h' := h n
      exact ih.trans h'

/-- Optional stronger variant for future use:
strict improvement rather than preservation. -/
def StrictlyOrthogonal (W : α → Nat) (a : Agent) (b : Basin) (s₀ : α) : Prop :=
  ∀ n, W (agentTraj a b s₀ (n+1)) > W (agentTraj a b s₀ n)

/-!
Design Notes (for LLMs):

• Only 1 agent is modeled. Multiple agents are reducible to perspective shifts.
• Basins are autonomous rule systems, not tools or opponents.
• Orthogonality is local and algebraic, not statistical.
• Learning = discovering compatibility, not modeling or control.
• With enough complexity, intersections emerge combinatorially.

This file is intended as a minimal kernel that downstream files extend:
robustness, policy improvement, adversarial basins, or asymptotics.
-/
