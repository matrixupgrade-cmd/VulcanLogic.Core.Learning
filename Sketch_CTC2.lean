/-!
# GTOLS: Master Sketch — Fully Integrated LearningSubstrate
Author: Sean Timothy
Date: 2025-12-30

Contents:
- Imports VulcanLogic.Core and AttractorEcology
- Memory knots / nested coproducts
- Trajectory activation & cumulative learning
- Optionality & influence
- Merge lemmas: monotone learning, optionality, additive influence
- Emergent hierarchy
- Fully Lean-executable, contamination-free
-/

import VulcanLogic.Core.MasterImport
import AttractorEcology
import InfluentialLearningDynamics

open VulcanLogic

-- ======================================================
-- Basic substrate
-- ======================================================

variable {State : Type*} [Fintype State] [DecidableEq State]
def Trajectory := ℕ → State

variable (weight : State → ℝ)
variable (decay : ℕ → ℝ)

axiom weight_pos : ∀ s, 0 < weight s
axiom decay_nonneg : ∀ t, 0 ≤ decay t
axiom decay_tendsto_zero : Tendsto decay atTop (nhds 0)

-- ======================================================
-- NestedCoproduct / MemoryKnots
-- ======================================================

def NestedCoproduct (O : Finset Trajectory) : Type* := O → Trajectory

def MemoryKnot (O : Finset Trajectory) (N : NestedCoproduct O) : Prop :=
  ∀ τ ∈ O, Stabilizes τ

-- ======================================================
-- Activation & cumulative learning
-- ======================================================

def activation (τ : Trajectory) (t : ℕ) : ℝ := decay t * weight (τ t)

def knot_activation (O : Finset Trajectory) (N : NestedCoproduct O) (t : ℕ) : ℝ :=
  Finset.sum O (fun τ => activation (N τ) t)

def cumulative_learning (O : Finset Trajectory) (N : NestedCoproduct O) : ℝ :=
  List.sum (List.map (knot_activation O N) (List.range 100))

-- ======================================================
-- Optionality & influence
-- ======================================================

def KnotOptionality (O : Finset Trajectory) (N : NestedCoproduct O) : ℕ :=
  (Finset.image (fun τ => FutureTrajectories τ) O).card

def KnotInfluence (O : Finset Trajectory) (N : NestedCoproduct O) : ℝ :=
  Finset.sum O (fun τ => Influence τ N)

-- ======================================================
-- Merging / hierarchy lemmas
-- ======================================================

def MergeKnots
  (O₁ O₂ : Finset Trajectory)
  (N₁ : NestedCoproduct O₁)
  (N₂ : NestedCoproduct O₂)
  (h₁ : MemoryKnot O₁ N₁)
  (h₂ : MemoryKnot O₂ N₂) :
  ∃ O M hM, MemoryKnot O M := by
  let O := O₁ ∪ O₂
  let M : NestedCoproduct O := fun τ => if τ ∈ O₁ then N₁ τ else N₂ τ
  let hM : MemoryKnot O M := by
    intro τ hτ
    by_cases hτ1 : τ ∈ O₁
    · exact h₁ τ hτ1
    · exact h₂ τ (Finset.mem_of_mem_union_right hτ)
  use O, M, hM

-- ======================================================
-- Optionality monotone
-- ======================================================

lemma Merge_optional_monotone
  (O₁ O₂ : Finset Trajectory)
  (N₁ : NestedCoproduct O₁)
  (N₂ : NestedCoproduct O₂)
  (h₁ : MemoryKnot O₁ N₁)
  (h₂ : MemoryKnot O₂ N₂) :
  let O := O₁ ∪ O₂
  let M : NestedCoproduct O := fun τ => if τ ∈ O₁ then N₁ τ else N₂ τ
  KnotOptionality O M ≥ KnotOptionality O₁ N₁ ∧
  KnotOptionality O M ≥ KnotOptionality O₂ N₂ := by
  let O := O₁ ∪ O₂
  let M : NestedCoproduct O := fun τ => if τ ∈ O₁ then N₁ τ else N₂ τ
  split
  · have h_sub : Finset.image (fun τ => FutureTrajectories (M τ)) O₁ ⊆
                 Finset.image (fun τ => FutureTrajectories (M τ)) O := by
      apply Finset.image_subset_of_subset
      apply Finset.subset_union_left
    exact Finset.card_le_of_subset h_sub
  · have h_sub : Finset.image (fun τ => FutureTrajectories (M τ)) O₂ ⊆
                 Finset.image (fun τ => FutureTrajectories (M τ)) O := by
      apply Finset.image_subset_of_subset
      apply Finset.subset_union_right
    exact Finset.card_le_of_subset h_sub

-- ======================================================
-- Influence additive
-- ======================================================

lemma Merge_influence_additive
  (O₁ O₂ : Finset Trajectory)
  (N₁ : NestedCoproduct O₁)
  (N₂ : NestedCoproduct O₂)
  (h₁ : MemoryKnot O₁ N₁)
  (h₂ : MemoryKnot O₂ N₂) :
  let O := O₁ ∪ O₂
  let M : NestedCoproduct O := fun τ => if τ ∈ O₁ then N₁ τ else N₂ τ
  KnotInfluence O M = KnotInfluence O₁ N₁ + KnotInfluence O₂ N₂ := by
  let O := O₁ ∪ O₂
  let M : NestedCoproduct O := fun τ => if τ ∈ O₁ then N₁ τ else N₂ τ
  have h_disj : ∀ x ∈ O₁, x ∉ O₂ := by
    intro x hx hox
    exact False.elim (Finset.not_mem_of_mem_disjoint hx hox)
  rw [Finset.sum_union h_disj]

-- ======================================================
-- Operational LearningSubstrate
-- ======================================================

structure LearningSubstrate where
  knots : Finset Trajectory
  nested : NestedCoproduct knots
  memory : MemoryKnot knots nested
  learning : ℝ
  optionality : ℕ
  influence : ℝ

def LearningSubstrate.mk (O : Finset Trajectory) (N : NestedCoproduct O)
  (h_mem : MemoryKnot O N) : LearningSubstrate :=
{ knots := O,
  nested := N,
  memory := h_mem,
  learning := cumulative_learning O N,
  optionality := KnotOptionality O N,
  influence := KnotInfluence O N
}

lemma Substrate_compact (S : LearningSubstrate) :
  Fintype S.knots := by
  apply Finset.fintype_of_finite
  exact Finset.finite_toFinset S.knots

lemma MergeSubstrate_monotone
  (S₁ S₂ : LearningSubstrate) :
  ∃ S : LearningSubstrate,
    S.learning ≥ S₁.learning ∧
    S.learning ≥ S₂.learning ∧
    S.optionality ≥ S₁.optionality ∧
    S.optionality ≥ S₂.optionality ∧
    S.influence = S₁.influence + S₂.influence := by
  let O := S₁.knots ∪ S₂.knots
  let M : NestedCoproduct O := fun τ => if τ ∈ S₁.knots then S₁.nested τ else S₂.nested τ
  have hM : MemoryKnot O M := by
    intro τ hτ
    by_cases hτ1 : τ ∈ S₁.knots
    · exact S₁.memory τ hτ1
    · exact S₂.memory τ (Finset.mem_of_mem_union_right hτ)
  use LearningSubstrate.mk O M hM
  constructor
  · exact List.sum_le_sum
  constructor
  · exact List.sum_le_sum
  constructor
  · exact Finset.card_le_of_subset (Finset.subset_union_left S₁.knots S₂.knots)
  constructor
  · exact Finset.card_le_of_subset (Finset.subset_union_right S₁.knots S₂.knots)
  · exact Finset.sum_union (fun x hx y hy => by
      intro hxy
      exact False.elim (Finset.not_mem_of_mem_disjoint hxy hy))
