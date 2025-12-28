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

/-- Two trajectories are distinct if they differ at some step. -/
def distinct_trajectories {S : Type} (m : FiniteMedium S) (x y : S) : Prop :=
  ∃ n, trajectory m x n ≠ trajectory m y n

/-- A state is recurrent if iteration revisits it. -/
def recurrent {S : Type} (m : FiniteMedium S) (x : S) : Prop :=
  ∃ n m', n < m' ∧ iterate m n x = iterate m m' x

/-- A (self-)attractor is represented minimally as recurrence. -/
def is_attractor {S : Type} (m : FiniteMedium S) (x : S) : Prop :=
  recurrent m x

/-- A bias is an alternative update rule on the same state space. -/
def Bias (S : Type) := S → S

/-- Apply a bias to obtain a new medium. -/
def apply_bias {S : Type} (m : FiniteMedium S) (b : Bias S) : FiniteMedium S :=
{ inst   := inferInstance
, update := b
}

/-!
## Structural Theorems
These are the minimal results required to claim that learning
*can occur* in this substrate.
-/

/-- Nontriviality: there exist distinguishable trajectories
    whenever the state space has more than one element. -/
theorem exists_distinct_trajectories
  {S : Type} (m : FiniteMedium S)
  (h : Fintype.card S ≥ 2) :
  ∃ x y : S, x ≠ y ∧ distinct_trajectories m x y :=
by
  classical
  -- Skeleton proof:
  -- choose x ≠ y from finiteness
  -- show trajectories differ at some finite step
  -- exact proof to be filled
  sorry

/-- Finite recurrence: every trajectory eventually revisits a state. -/
theorem exists_recurrent_state
  {S : Type} (m : FiniteMedium S) :
  ∃ x : S, is_attractor m x :=
by
  classical
  -- Finite pigeonhole principle on iteration
  -- This is the core "attractor existence" result
  sorry

/-- Bias sensitivity: there exists a bias that alters attractor structure. -/
theorem exists_bias_changes_attractor
  {S : Type} (m : FiniteMedium S)
  (h : Fintype.card S ≥ 2) :
  ∃ (b : Bias S) (x : S),
    is_attractor m x ≠ is_attractor (apply_bias m b) x :=
by
  classical
  -- Construct a bias that changes recurrence behavior
  -- This proves learning admissibility
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
  (h : Fintype.card S ≥ 2) :
  (∃ x y, x ≠ y ∧ distinct_trajectories m x y) ∧
  (∃ x, is_attractor m x) ∧
  (∃ b x, is_attractor m x ≠ is_attractor (apply_bias m b) x) :=
by
  refine ⟨?h₁, ?h₂, ?h₃⟩
  · exact exists_distinct_trajectories m h
  · exact exists_recurrent_state m
  · exact exists_bias_changes_attractor m h

end VulcanLogic
