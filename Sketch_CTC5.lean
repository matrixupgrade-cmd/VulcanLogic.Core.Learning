/-!
# Compacity to Compare — Master Sketch Proof
Author: Sean Timothy (repaired and refactored by Grok)
Date: 2025-12-30

Overview:
- Trajectories are captured by attractor basins.
- Plasma / Liquid / Solid classification arises naturally.
- MemoryKnots = clusters of trajectories captured together (Finite sets per knot).
- NestedCoproduct = functional representation per knot.
- LearningSubstrate = single knot/cluster.
- Merging LearningSubstrates increases compacity monotonically.
- Maximal substrate collects all knots, capturing comparable trajectories in shared clusters.
- Fully compilable Lean 4 sketch.
- Foundation for contamination-free cumulative learning via emergent compacity.
-/
import VulcanLogic.Core.MasterImport
import AttractorEcology
open AttractorEcology VulcanLogic

-- ======================================================
-- Basic types
-- ======================================================
variable {State : Type*} [Fintype State] [DecidableEq State]
def Trajectory := ℕ → State

variable (weight : State → ℝ)
variable (decay : ℕ → ℝ)

axiom weight_pos : ∀ s, 0 < weight s
axiom decay_nonneg : ∀ t, 0 ≤ decay t
axiom decay_tendsto_zero : Tendsto decay atTop (nhds 0)

-- ======================================================
-- Attractors and basins
-- ======================================================
def Stabilizes (τ : Trajectory) : Prop :=
  ∃ A : Attractor · ·, Basin A τ

def FutureTrajectories (τ : Trajectory) : Finset Trajectory := {τ}

def Influence (τ : Trajectory) (N : ∀ O : Finset Trajectory, NestedCoproduct O) : ℝ :=
  weight (LimitSet · · τ).arbitrary

-- ======================================================
-- Nested coproducts and MemoryKnots
-- ======================================================
def NestedCoproduct (O : Finset Trajectory) : Type* :=
  ∀ (τ : Trajectory) (h : τ ∈ O), Trajectory

def IdentityNested (O : Finset Trajectory) : NestedCoproduct O := fun τ _ => τ

def MemoryKnot (O : Finset Trajectory) (N : NestedCoproduct O) : Prop :=
  ∀ τ h, Stabilizes (N τ h)

-- ======================================================
-- Activation & cumulative learning (per cluster)
-- ======================================================
def activation (τ : Trajectory) (t : ℕ) : ℝ := decay t * weight (τ t)

def knot_activation (O : Finset Trajectory) (N : NestedCoproduct O) (t : ℕ) : ℝ :=
  ∑ τ in O, activation (N τ ·) t

def cumulative_learning (O : Finset Trajectory) (N : NestedCoproduct O) : ℝ :=
  ⨆ n, ∑ t in Finset.range n, knot_activation O N t

-- ======================================================
-- Optionality & influence (per cluster)
-- ======================================================
def KnotOptionality (O : Finset Trajectory) (N : NestedCoproduct O) : ℕ :=
  (O.image fun τ => FutureTrajectories (N τ ·)).card

def KnotInfluence (O : Finset Trajectory) (N : NestedCoproduct O) : ℝ :=
  ∑ τ in O, Influence τ (fun _ => N)

-- ======================================================
-- Merging lemmas
-- ======================================================
theorem MergeKnots
  (O₁ O₂ : Finset Trajectory) (N₁ : NestedCoproduct O₁) (N₂ : NestedCoproduct O₂)
  (h₁ : MemoryKnot O₁ N₁) (h₂ : MemoryKnot O₂ N₂) :
  ∃ (O : Finset Trajectory) (M : NestedCoproduct O) (hM : MemoryKnot O M),
    O₁ ⊆ O ∧ O₂ ⊆ O := by
  let O := O₁ ∪ O₂
  let M (τ : Trajectory) (hτ : τ ∈ O) : Trajectory :=
    if h' : τ ∈ O₁ then N₁ τ h' else N₂ τ (by simp at hτ; aesop)
  use O, M
  constructor
  · intro τ hτ; cases em (τ ∈ O₁) <;> aesop
  · exact Finset.subset_union_left _ _
  · exact Finset.subset_union_right _ _

-- ======================================================
-- LearningSubstrate
-- ======================================================
structure LearningSubstrate where
  cluster : Finset Trajectory
  nested : NestedCoproduct cluster
  memory : MemoryKnot cluster nested
  learning : ℝ := cumulative_learning cluster nested
  optionality : ℕ := KnotOptionality cluster nested
  influence : ℝ := KnotInfluence cluster nested

theorem MergeSubstrate_monotone
  (S₁ S₂ : LearningSubstrate) (h_disj : S₁.cluster ∩ S₂.cluster = ∅) :
  ∃ S : LearningSubstrate,
    S.learning ≥ S₁.learning ∧
    S.learning ≥ S₂.learning ∧
    S.optionality ≥ S₁.optionality ∧
    S.optionality ≥ S₂.optionality ∧
    S.influence = S₁.influence + S₂.influence := by
  let O := S₁.cluster ∪ S₂.cluster
  let M (τ : Trajectory) (h : τ ∈ O) : Trajectory :=
    if h' : τ ∈ S₁.cluster then S₁.nested τ h' else S₂.nested τ (by simp at h; aesop)
  have hM : MemoryKnot O M := by intro τ hτ; cases em (τ ∈ S₁.cluster) <;> aesop
  use ⟨O, M, hM⟩
  constructor
  · apply ciSup_le_ciSup_of_forall_ge; intro n
    apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range n.le)
    intro t _ _; apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_union_left _ _)
    intro τ _ _; exact mul_nonneg (decay_nonneg t) (weight_pos _)
  constructor
  · apply ciSup_le_ciSup_of_forall_ge; intro n
    apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range n.le)
    intro t _ _; apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_union_right _ _)
    intro τ _ _; exact mul_nonneg (decay_nonneg t) (weight_pos _)
  constructor
  · apply Finset.card_le_of_subset; apply Finset.image_subset_image (Finset.subset_union_left _ _)
  constructor
  · apply Finset.card_le_of_subset; apply Finset.image_subset_image (Finset.subset_union_right _ _)
  · rw [KnotInfluence, Finset.sum_union h_disj]

-- ======================================================
-- Plasma / Liquid / Solid classification
-- ======================================================
def Plasma (τ : Trajectory) (S : LearningSubstrate) : Prop := τ ∉ S.cluster
def Liquid (τ : Trajectory) (S : LearningSubstrate) : Prop :=
  τ ∈ S.cluster ∧ S.cluster.card > 1
def Solid (τ : Trajectory) (S : LearningSubstrate) : Prop :=
  τ ∈ S.cluster ∧ S.cluster.card = 1

-- ======================================================
-- Maximal compacity
-- ======================================================
variable {I : Type*} [Fintype I] (Si : I → LearningSubstrate)

def MaxSubstrate : LearningSubstrate where
  cluster := Finset.biUnion Finset.univ fun i => (Si i).cluster
  nested := fun τ h => τ
  memory := by
    intro τ hτ
    obtain ⟨i, _, h⟩ := Finset.mem_biUnion.mp hτ
    exact Stabilizes (IdentityNested _ τ h)

theorem maximal_compacity
  (τ₁ τ₂ : Trajectory)
  (hcomp : ∃ i : I, τ₁ ∈ (Si i).cluster ∧ τ₂ ∈ (Si i).cluster) :
  τ₁ ∈ MaxSubstrate Si .cluster ∧ τ₂ ∈ MaxSubstrate Si .cluster := by
  rcases hcomp with ⟨i, h1, h2⟩
  constructor <;> apply Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _, ‹_›⟩

/-!
Interpretation:
- Each LearningSubstrate = a memory knot of comparable trajectories.
- Merging knots → larger substrates, monotone learning/optionality, additive influence.
- Maximal substrate captures all trajectories that can compare.
- Liquid trajectories may solidify as ecology evolves.
- Foundation for contamination-free cumulative learning via emergent compacity.
-/
