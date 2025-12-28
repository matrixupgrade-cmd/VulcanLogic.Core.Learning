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

/-- A state is recurrent if iteration returns to it. -/
def recurrent {S : Type} (m : FiniteMedium S) (x : S) : Prop :=
  ∃ (k : ℕ) (hk : 0 < k), iterate m k x = x

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

lemma iterate_add {S : Type} (m : FiniteMedium S) (n k : ℕ) (x : S) :
  iterate m (n + k) x = iterate m k (iterate m n x) := by
  induction' k with k ih
  · rfl
  · simp [Nat.succ_eq_add_one, ← Nat.add_assoc, iterate, ih]

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
  {S : Type} [Nonempty S] (m : FiniteMedium S) :
  ∃ x : S, is_attractor m x :=
by
  classical
  by_contra h
  push_neg at h
  let x : S := Classical.arbitrary S
  have hinj : Function.Injective (trajectory m x) := by
    intro n m' heq
    wlog hnm : n ≤ m' generalizing n m'
    · exact (this (heq.symm) (Nat.le_of_not_le hnm)).symm
    obtain rfl | hlt := eq_or_lt_of_le hnm
    · rfl
    have hsub : 0 < m' - n := Nat.sub_pos_of_lt hlt
    have hneq := h (iterate m n x) (m' - n) hsub
    simp only [trajectory, ne_eq] at hneq
    rw [iterate_add] at hneq
    rw [heq] at hneq
    exact hneq rfl
  have : Infinite S := Infinite.of_injective (trajectory m x) hinj
  exact Finite.not_infinite this

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
  haveI : Nonempty S := Fintype.card_pos_iff.mp (by linarith)
  obtain ⟨z, hz⟩ := exists_recurrent_state m
  have hex : ∃ (w : S), w ≠ z := by
    simp [Fintype.exists_ne z]
  let w : S := Classical.choose hex
  have hw : w ≠ z := Classical.choose_spec hex
  let b : Bias S := fun _ => w
  let m' := apply_bias m b
  refine ⟨b, z, ?_⟩
  rw [hz]
  simp [is_attractor, recurrent]
  push_neg
  intro k hk heq
  cases k with
  | zero =>
    exact Nat.lt_irrefl _ hk
  | succ k =>
    simp [iterate] at heq
    have : m'.update z = w := rfl
    rw [this] at heq
    have ih : ∀ l > 0, iterate m' l w = w := by
      intro l hl
      induction' l with l' ihl' generalizing hl
      · simp at hl
      · cases l'
        · simp [iterate]
        · simp [iterate, ihl' (Nat.succ_pos _)]
    rw [ih (k + 1) (Nat.succ_pos _)] at heq
    exact hw.symm heq

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
  haveI : Nonempty S := Fintype.card_pos_iff.mp (by linarith)
  refine ⟨?h₁, ?h₂, ?h₃⟩
  · exact exists_distinct_trajectories m h_card h_nontrivial
  · exact exists_recurrent_state m
  · exact exists_bias_changes_attractor m h_card

end VulcanLogic
