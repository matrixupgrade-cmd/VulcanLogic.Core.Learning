/-
# Attractor Learning Substrate
AttractorLearningSubstrate.lean

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
  | n + 1 => m.update ∘ iterate n

/-- The forward trajectory of a state under iteration. -/
def trajectory {S : Type} (m : FiniteMedium S) (x : S) : ℕ → S :=
  fun n => iterate m n x

/-- Two trajectories diverge if they differ at some finite step. -/
def diverging_trajectories {S : Type} (m : FiniteMedium S) (x y : S) : Prop :=
  ∃ n, trajectory m x n ≠ trajectory m y n

/-- A state is recurrent if iteration returns to it after a positive number of steps. -/
def recurrent {S : Type} (m : FiniteMedium S) (x : S) : Prop :=
  ∃ k > 0, iterate m k x = x

/-- A (self-)attractor is minimally represented as recurrence. -/
def is_attractor {S : Type} (m : FiniteMedium S) (x : S) : Prop :=
  recurrent m x

/-- A bias is an alternative update rule on the same state space. -/
def Bias (S : Type) := S → S

/-- Apply a bias to obtain a new medium. -/
def apply_bias {S : Type} (m : FiniteMedium S) (b : Bias S) : FiniteMedium S :=
  { inst   := inferInstance
    update := b }

@[simp]
lemma iterate_add {S : Type} (m : FiniteMedium S) (n k : ℕ) (x : S) :
    iterate m (n + k) x = iterate m k (iterate m n x) := by
  induction' k with k ih
  · rfl
  · simp [iterate, Function.comp, ih]

--------------------------------------------------------------------------------
-- Structural Theorems
--------------------------------------------------------------------------------

/--
Nontriviality of trajectories.

If the update rule sends at least two distinct states to distinct successors,
then there exist distinct states with diverging trajectories.
-/
theorem exists_diverging_trajectories
    {S : Type} (m : FiniteMedium S)
    (h_nontrivial : ∃ x y : S, x ≠ y ∧ m.update x ≠ m.update y) :
    ∃ x y : S, x ≠ y ∧ diverging_trajectories m x y := by
  obtain ⟨x, y, hxy, hUpd⟩ := h_nontrivial
  exact ⟨x, y, hxy, 1, by simp [trajectory, iterate, hUpd]⟩

/--
Finite recurrence.

Every nonempty finite dynamical medium admits at least one recurrent state
(and hence at least one self-attractor).
-/
theorem exists_recurrent_state
    {S : Type} [Nonempty S] (m : FiniteMedium S) :
    ∃ x : S, is_attractor m x := by
  classical
  by_contra h_no
  push_neg at h_no
  let x₀ : S := Classical.arbitrary S
  have inj : Function.Injective (trajectory m x₀) := by
    intro i j h_eq
    without_loss_of_generality assume i ≤ j
    cases eq_or_lt_of_le ‹i ≤ j›
    · assumption
    · let d := j - i
      have hd : d > 0 := Nat.sub_pos_of_lt ‹i < j›
      have contra := h_no (iterate m i x₀) d hd
      rw [iterate_add, h_eq] at contra
      exact contra rfl
  have := Infinite.of_injective (trajectory m x₀) inj
  exact not_infinite S this

/--
Bias sensitivity of attractor structure.

In any medium with at least two states, there exists a bias that changes
whether a particular state is an attractor.
-/
theorem exists_bias_changes_attractor
    {S : Type} (m : FiniteMedium S)
    (h_card : Fintype.card S ≥ 2) :
    ∃ (b : Bias S) (x : S),
      is_attractor m x ≠ is_attractor (apply_bias m b) x := by
  classical
  haveI := Fintype.card_pos_iff.mp (by linarith)
  obtain ⟨z, hz⟩ := exists_recurrent_state m
  obtain ⟨w, hw⟩ : ∃ w : S, w ≠ z := Fintype.exists_ne z
  let b : Bias S := fun _ => w
  let m' := apply_bias m b
  use b, z
  constructor
  · exact hz
  · simp only [is_attractor, recurrent, m', apply_bias, b]
    push_neg
    rintro ⟨k, hk, h_iter⟩
    cases k
    · exact Nat.not_lt_zero _ hk
    · simp [iterate] at h_iter
      have : iterate m' (k + 1) w = w := by
        induction' k with k ih
        · simp [iterate]
        · simp [iterate, ih]
      rw [← h_iter, this]
      exact hw

/--
Learning Admissibility Theorem.

Under minimal nontriviality assumptions, a finite medium admits:
• diverging trajectories
• attractors
• bias-sensitive attractor structure
-/
theorem learning_admissible
    {S : Type} (m : FiniteMedium S)
    (h_card : Fintype.card S ≥ 2)
    (h_nontrivial : ∃ x y : S, x ≠ y ∧ m.update x ≠ m.update y) :
    (∃ x y, x ≠ y ∧ diverging_trajectories m x y) ∧
    (∃ x, is_attractor m x) ∧
    (∃ b x, is_attractor m x ≠ is_attractor (apply_bias m b) x) := by
  haveI := Fintype.card_pos_iff.mp (by linarith)
  exact ⟨exists_diverging_trajectories m h_nontrivial,
         exists_recurrent_state m,
         exists_bias_changes_attractor m h_card⟩

end VulcanLogic
