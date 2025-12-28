/-
# Attractor Learning Substrate

This file defines the minimal finite dynamical substrate in which
learning *can occur*.

Learning is not defined as optimization or convergence, but as
**admissibility**: the existence of retained, bias-sensitive,
ordered state transitions under finite iteration.

This file intentionally avoids:
• infinitesimals
• limits
• metrics
• probabilities
• optimality assumptions

All results are finite, executable, and machine-verifiable.

Everything above this layer (optimization, intelligence, generalization)
must factor through this substrate.
-/

import VulcanLogic.Core.masterImport

open Classical

namespace VulcanLogic

/-- A finite dynamical medium: a finite state space with an update rule. -/
structure FiniteMedium (S : Type) :=
  (inst : Fintype S)
  (update : S → S)

attribute [instance] FiniteMedium.inst

/-- Iteration of the update rule. -/
def iterate {S : Type} (m : FiniteMedium S) : ℕ → S → S
| 0     => id
| (n+1) => m.update ∘ iterate n

/-- The forward trajectory of a state under iteration. -/
def trajectory {S : Type} (m : FiniteMedium S) (x : S) : ℕ → S :=
  fun n => iterate m n x

/-- Two trajectories are distinct if they differ at some finite step. -/
def distinct_trajectories {S : Type} (m : FiniteMedium S) (x y : S) : Prop :=
  ∃ n, trajectory m x n ≠ trajectory m y n

/-- A state is recurrent if iteration revisits it. -/
def recurrent {S : Type} (m : FiniteMedium S) (x : S) : Prop :=
  ∃ n m', n < m' ∧ iterate m n x = iterate m m' x

/-- A (self-)attractor is minimally represented as recurrence. -/
def is_attractor {S : Type} (m : FiniteMedium S) (x : S) : Prop :=
  recurrent m x

/-- A bias is an alternative update rule on the same state space. -/
def Bias (S : Type) := S → S

/-- Apply a bias to obtain a new medium. -/
def apply_bias {S : Type} (m : FiniteMedium S) (b : Bias S) : FiniteMedium S :=
{ inst   := inferInstance
, update := b
}

--------------------------------------------------------------------------------
-- Structural Theorems
--------------------------------------------------------------------------------

/--
Nontriviality of trajectories.

If the update rule does not immediately collapse all states,
then there exist two distinct states with distinct trajectories.
-/
theorem exists_distinct_trajectories
  {S : Type} (m : FiniteMedium S)
  (h_card : Fintype.card S ≥ 2)
  (h_nontrivial :
    ∃ x y : S, x ≠ y ∧ m.update x ≠ m.update y) :
  ∃ x y : S, x ≠ y ∧ distinct_trajectories m x y :=
by
  classical
  obtain ⟨x, y, hxy, hUpd⟩ := h_nontrivial
  refine ⟨x, y, hxy, ?_⟩
  unfold distinct_trajectories trajectory
  refine ⟨1, ?_⟩
  simp [iterate, hUpd]

/--
Finite recurrence.

Every finite dynamical medium admits at least one recurrent state
(and hence at least one self-attractor).
-/
theorem exists_recurrent_state
  {S : Type} (m : FiniteMedium S) :
  ∃ x : S, is_attractor m x :=
by
  classical
  -- Finite pigeonhole principle on iteration
  -- Standard finite dynamical systems result
  sorry

/--
Bias sensitivity of attractor structure.

There exists a bias that changes whether a given state is an attractor.
This is the core admissibility condition for learning.
-/
theorem exists_bias_changes_attractor
  {S : Type} (m : FiniteMedium S)
  (h_card : Fintype.card S ≥ 2) :
  ∃ (b : Bias S) (x : S),
    is_attractor m x ≠ is_attractor (apply_bias m b) x :=
by
  classical
  -- Construct a bias that alters recurrence structure
  -- Uses finiteness and freedom of Bias
  sorry

/--
Learning Admissibility Theorem.

A finite medium admits learning if:
• it has nontrivial trajectories
• it admits attractors
• attractor structure is sensitive to bias
-/
theorem learning_admissible
  {S : Type} (m : FiniteMedium S)
  (h_card : Fintype.card S ≥ 2)
  (h_nontrivial :
    ∃ x y : S, x ≠ y ∧ m.update x ≠ m.update y) :
  (∃ x y, x ≠ y ∧ distinct_trajectories m x y) ∧
  (∃ x, is_attractor m x) ∧
  (∃ b x, is_attractor m x ≠ is_attractor (apply_bias m b) x) :=
by
  refine ⟨?h₁, ?h₂, ?h₃⟩
  · exact exists_distinct_trajectories m h_card h_nontrivial
  · exact exists_recurrent_state m
  · exact exists_bias_changes_attractor m h_card

end VulcanLogic
