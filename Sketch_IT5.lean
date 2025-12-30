/-!
===============================================================================
MasterLean.lean
Finite Nested Ecology Dynamics — Influential Trajectories, Fading, and Meta-Learning
Author: Grok + Sean Hitch
Date: 2025-12-29
Notes:
- Time is treated as discrete iterations (ℕ), keeping all sets finite.
- Supports nested ecologies with delayed interactions.
- Tracks fading, influence, cumulative learning, and meta-learning capacity.
- Ready for further Lean verification or concrete examples.
===============================================================================
-/

import Mathlib.Data.Real.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.List.Basic
import Mathlib.Analysis.Asymptotics.Asymptotics

open Finset List

variable {State : Type} [Fintype State] [DecidableEq State] [Inhabited State]
variable {Operator : Type} [Fintype Operator] [DecidableEq Operator]
variable {Signal : Type} [Fintype Signal] [DecidableEq Signal]

-- ========================================================================
-- Basic Definitions
-- ========================================================================

def Trajectory := ℕ → State

-- Step function, input, weight, decay
variable (step : Operator → State → Signal → State)
variable (input : ℕ → Signal)
variable (weight : State → ℝ)
variable (decay : ℕ → ℝ)

axiom weight_pos : ∀ s, 0 < weight s
axiom decay_nonneg : ∀ t, 0 ≤ decay t
axiom decay_pos_finite : ∀ t, 0 < decay t
axiom decay_tendsto_zero : Tendsto decay atTop (nhds 0)

-- Activation at iteration t
def activation (τ : Trajectory) (t : ℕ) : ℝ := decay t * weight (τ t)

-- Fading predicate
def fades (τ : Trajectory) : Prop :=
  ∀ ε > 0, ∃ T, ∀ t ≥ T, activation τ t < ε

-- ========================================================================
-- Ecology Structure
-- ========================================================================

structure Ecology where
  name : String
  states : Finset State
  basin  : State → Prop
  weight_update : State → ℝ → State → ℝ
  learning_nontrivial : ∀ (s ∈ states) (infl > 0), weight_update s infl s ≠ weight s
  interactions : List (Ecology × ℕ)  -- (target ecology, delay)

-- Influence if trajectory enters any state in the ecology
def influences_local_ecology (E : Ecology) (τ : Trajectory) : Prop :=
  ∃ t, τ t ∈ E.states

-- Delayed trajectory (shift by d iterations)
def delayed_τ (τ : Trajectory) (d : ℕ) : Trajectory :=
  fun k => τ (k + d)

-- Cumulative learning: local + nested ecology contributions
def cumulative_learning : Ecology → Trajectory → ℝ
| E, τ =>
  let local := List.sum (List.map (activation τ) (List.range 100))
  let nested := List.sum (E.interactions.map (fun (E', d) => cumulative_learning E' (delayed_τ τ d)))
  local + nested

-- Trajectory induces learning in ecology
def induces_learning (E : Ecology) (τ : Trajectory) : Prop :=
  let infl := cumulative_learning E τ
  infl > 0 ∧ ∃ s ∈ E.states, E.weight_update s infl s ≠ weight s

-- Influential trajectory
def influential_trajectory (E : Ecology) (τ : Trajectory) : Prop :=
  influences_local_ecology E τ ∧ induces_learning E τ

-- ========================================================================
-- Dominant Trajectories and Meta-Learning
-- ========================================================================

-- Dominant trajectory among a list
def dominant_trajectory (E : Ecology) (trajectories : List Trajectory) : Option Trajectory :=
  trajectories.argmax (cumulative_learning E)

-- Max cumulative learning
def max_learning (E : Ecology) (trajectories : List Trajectory) : ℝ :=
  List.foldr (fun τ m => max (cumulative_learning E τ) m) 0 trajectories

-- List of dominant trajectories
def dominant_trajectories (E : Ecology) (trajectories : List Trajectory) : List Trajectory :=
  trajectories.filter (fun τ => cumulative_learning E τ = max_learning E trajectories)

-- Meta-learning capacity: sum over dominant trajectories
def meta_learning_capacity (E : Ecology) (trajectories : List Trajectory) : ℝ :=
  List.sum (dominant_trajectories E trajectories).map (cumulative_learning E)

-- ========================================================================
-- Theorems and Lemmas
-- ========================================================================

-- Suppressed trajectory fades
lemma suppressed_trajectory_fades
  (E : Ecology)
  (trajectories : List Trajectory)
  (τ : Trajectory)
  (hτ : τ ∈ trajectories)
  (h_sup : cumulative_learning E τ < max_learning E trajectories) :
  fades τ :=
by
  intro ε ε_pos
  obtain ⟨T, hT⟩ := decay_tendsto_zero ε_pos
  use T
  intro t ht
  let w_max := Finset.sup univ weight
  have hw_max : ∀ s, weight s ≤ w_max := Finset.le_sup (mem_univ _)
  have w_max_pos : 0 ≤ w_max := Finset.sup_nonneg (fun _ => by linarith [weight_pos _])
  calc activation τ t
    = decay t * weight (τ t) := rfl
    _ ≤ decay t * w_max := mul_le_mul_of_nonneg_left (hw_max (τ t)) (decay_nonneg t)
    _ < ε := hT t ht

-- Trend lifecycle: every trajectory either dominates or fades
theorem trend_lifecycle
  (E : Ecology)
  (trajectories : List Trajectory)
  (h_nonempty : trajectories ≠ []) :
  ∀ τ ∈ trajectories,
    cumulative_learning E τ = max_learning E trajectories ∨ fades τ :=
by
  intro τ hτ
  by_cases h_dom : cumulative_learning E τ = max_learning E trajectories
  · left
    exact h_dom
  · right
    have lt_max : cumulative_learning E τ < max_learning E trajectories :=
      lt_of_le_of_ne (le_max_learning E trajectories hτ) (Ne.symm h_dom)
    exact suppressed_trajectory_fades E trajectories τ hτ lt_max

-- Meta-learning capacity is non-negative
lemma meta_learning_capacity_nonneg
  (E : Ecology)
  (trajectories : List Trajectory) :
  0 ≤ meta_learning_capacity E trajectories :=
by
  unfold meta_learning_capacity
  apply sum_nonneg
  intro τ _; apply sum_nonneg
  intro _ _; apply mul_nonneg (decay_nonneg _) (by linarith [weight_pos _])

-- Bounded meta-learning (sketch; requires finite nesting depth)
lemma meta_learning_capacity_bounded
  (E : Ecology)
  (trajectories : List Trajectory) :
  meta_learning_capacity E trajectories ≤
    List.length trajectories *
    List.sum (List.map (fun t => decay t * Finset.sup univ weight) (List.range 100)) *
    (1 + Nat.land E.interactions.length) ^ E.interactions.length :=
by
  sorry

/-!
===============================================================================
Notes:
- Time is discrete iterations (ℕ) to guarantee finiteness.
- All sets (State, Signal, Operator) are finite.
- Supports fading, influential trajectories, nested ecologies, and meta-learning.
- Suppressed trajectories are guaranteed to fade under decay → 0.
- Dominant trajectories define the maximal learning and trend capacity.
- Meta-learning boundedness is sketched for finite nesting depth.
===============================================================================
-/
