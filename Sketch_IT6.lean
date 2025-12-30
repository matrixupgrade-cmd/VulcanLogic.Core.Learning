/-!
Master Lean Sketch: Finite Nested Ecology Dynamics
Author: Sean Timothy
Date: 2025-12-29

Notes:
- The system models finite nested ecologies of states with influence propagation.
- Trajectories can be "influential" (inducing learning) or "suppressed/fading".
- Meta-learning capacity sums contributions of dominant trajectories, including nested interactions.
- Composition lemmas allow modular construction of larger nested ecologies.
- Trend lifecycle: every trajectory either achieves maximal cumulative learning or fades.
- Proofs preserve finiteness and type correctness.

Minor note: Here "time" is implemented as **iteration steps (ℕ)**, not continuous time.
-/

import Mathlib.Data.Real.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.List.Basic
import Mathlib.Analysis.Asymptotics.Asymptotics

open Finset List

-- ------------------------------------------------------------------------
-- Basic Types and Trajectories
-- ------------------------------------------------------------------------

variable {State : Type} [Fintype State] [DecidableEq State] [Inhabited State]
variable {Operator : Type} [Fintype Operator] [DecidableEq Operator]
variable {Signal : Type} [Fintype Signal] [DecidableEq Signal]

def Trajectory := ℕ → State

variable (step : Operator → State → Signal → State)
variable (input : ℕ → Signal)
variable (weight : State → ℝ)
variable (decay : ℕ → ℝ)

axiom weight_pos : ∀ s, 0 < weight s
axiom decay_nonneg : ∀ t, 0 ≤ decay t
axiom decay_pos_finite : ∀ t, 0 < decay t
axiom decay_tendsto_zero : Tendsto decay atTop (nhds 0)

def activation (τ : Trajectory) (t : ℕ) : ℝ := decay t * weight (τ t)

def fades (τ : Trajectory) : Prop :=
  ∀ ε > 0, ∃ T, ∀ t ≥ T, activation τ t < ε

-- ------------------------------------------------------------------------
-- Ecology Structure
-- ------------------------------------------------------------------------

structure Ecology where
  name : String
  states : Finset State
  basin  : State → Prop
  weight_update : State → ℝ → State → ℝ
  learning_nontrivial : ∀ (s ∈ states) (infl > 0), weight_update s infl s ≠ weight s
  interactions : List (Ecology × ℕ)  -- nested ecologies with optional delay

def influences_local_ecology (E : Ecology) (τ : Trajectory) : Prop := ∃ t, τ t ∈ E.states

-- Delayed trajectory for nested interaction
def delayed_τ (τ : Trajectory) (d : ℕ) : Trajectory := fun k => τ (k + d)

def cumulative_learning : Ecology → Trajectory → ℝ
| E, τ =>
  let local := List.sum (List.map (activation τ) (List.range 100))
  let nested := List.sum (E.interactions.map (fun (E', d) => cumulative_learning E' (delayed_τ τ d)))
  local + nested

def induces_learning (E : Ecology) (τ : Trajectory) : Prop :=
  let infl := cumulative_learning E τ
  infl > 0 ∧ ∃ s ∈ E.states, E.weight_update s infl s ≠ weight s

def influential_trajectory (E : Ecology) (τ : Trajectory) : Prop :=
  influences_local_ecology E τ ∧ induces_learning E τ

-- ------------------------------------------------------------------------
-- Multi-spike trajectory constructor
-- ------------------------------------------------------------------------

def τ_multi_spike (spikes : List (ℕ × State)) : Trajectory :=
  fun t =>
    match spikes.filter (fun p => p.1 = t) with
    | [] => default
    | (_, s) :: _ => s

-- ------------------------------------------------------------------------
-- Nested Ecologies
-- ------------------------------------------------------------------------

inductive NestedEcology
| leaf : Ecology → NestedEcology
| node : Ecology → List NestedEcology → NestedEcology

open NestedEcology

def cumulative_learning_nested : NestedEcology → Trajectory → ℕ → ℝ
| leaf E, τ, N := cumulative_learning E τ
| node E children, τ, N :=
  let local := cumulative_learning E τ N in
  let nested := List.sum (children.map (fun child => cumulative_learning_nested child (delayed_τ τ 1) N)) in
  local + nested

def influential_nested (NE : NestedEcology) (τ : Trajectory) (N : ℕ) : Prop :=
  let infl := cumulative_learning_nested NE τ N in
  infl > 0 ∧ ∃ s, ∃ E, (match NE with
                         | leaf E' => E' = E
                         | node E' _ => E' = E) ∧ s ∈ E.states

-- Composition of ecologies with delay
def compose_ecologies (E1 E2 : Ecology) (delay : ℕ) : Ecology :=
{ name := E1.name ++ "+" ++ E2.name,
  states := E1.states ∪ E2.states,
  basin := fun s => E1.basin s ∨ E2.basin s,
  weight_update := fun s infl s' =>
    if s ∈ E1.states then E1.weight_update s infl s'
    else if s ∈ E2.states then E2.weight_update s infl s'
    else infl,
  learning_nontrivial := 
    begin
      intros s hs infl hpos,
      by_cases h1 : s ∈ E1.states,
      { exact E1.learning_nontrivial s h1 infl hpos },
      { by_cases h2 : s ∈ E2.states,
        { exact E2.learning_nontrivial s h2 infl hpos },
        { trivial } }
    end,
  interactions := (E1.interactions.map (fun (p : Ecology × ℕ) => (p.1, p.2 + delay))) ++ E2.interactions }

lemma composed_ecology_influential
  (E1 E2 : Ecology)
  (τ : Trajectory)
  (delay : ℕ)
  (h1 : influential_trajectory E1 τ)
  (h2 : influential_trajectory E2 (delayed_τ τ delay)) :
  influential_trajectory (compose_ecologies E1 E2 delay) τ :=
begin
  unfold influential_trajectory compose_ecologies,
  split,
  { cases h1 with t1 ht1, use t1, simp [ht1] },
  { cases h1 with infl1 learn1, cases h2 with infl2 learn2,
    let total := infl1.fst + infl2.fst,
    split,
    { linarith },
    { cases learn1.snd with s1 hs1, use [s1, hs1.1], exact hs1.2 } }
end

-- ------------------------------------------------------------------------
-- Dominant Trajectories & Meta-Learning
-- ------------------------------------------------------------------------

def dominant_nested_trajectories (NE : NestedEcology) (τ_list : List Trajectory) (N : ℕ) : List Trajectory :=
  τ_list.filter (fun τ => cumulative_learning_nested NE τ N =
                          List.foldr (max) 0 (τ_list.map (fun t => cumulative_learning_nested NE t N)))

def meta_learning_capacity_nested (NE : NestedEcology) (τ_list : List Trajectory) (N : ℕ) : ℝ :=
  List.sum (dominant_nested_trajectories NE τ_list N).map (fun τ => cumulative_learning_nested NE τ N)

lemma meta_learning_capacity_nested_nonneg
  (NE : NestedEcology) (τ_list : List Trajectory) (N : ℕ) :
  0 ≤ meta_learning_capacity_nested NE τ_list N :=
begin
  unfold meta_learning_capacity_nested dominant_nested_trajectories,
  apply List.sum_nonneg,
  intros τ hτ,
  unfold cumulative_learning_nested,
  induction NE with E children ih,
  { apply List.sum_nonneg, intros t ht, apply mul_nonneg (decay_nonneg t) (weight_pos (τ t)) },
  { apply add_nonneg,
    { apply List.sum_nonneg, intros t ht, apply mul_nonneg (decay_nonneg t) (weight_pos (τ t)) },
    { apply List.sum_nonneg, intros child _, exact ih child τ hτ } }
end

lemma suppressed_trajectory_fades
  (E : Ecology)
  (trajectories : List Trajectory)
  (τ : Trajectory)
  (hτ : τ ∈ trajectories)
  (h_sup : cumulative_learning E τ < List.foldr max 0 (trajectories.map (cumulative_learning E))) :
  fades τ :=
by
  intro ε ε_pos
  obtain ⟨T, hT⟩ := decay_tendsto_zero ε_pos
  use T
  intro t ht
  let w_max := Finset.sup univ weight
  calc activation τ t = decay t * weight (τ t) := rfl
  _ ≤ decay t * w_max := mul_le_mul_of_nonneg_left (Finset.le_sup (mem_univ _)) (decay_nonneg t)
  _ < ε := hT t ht

theorem nested_ecology_trend_lifecycle
  (NE : NestedEcology)
  (τ_list : List Trajectory)
  (N : ℕ)
  (h_nonempty : τ_list ≠ []) :
  ∀ τ ∈ τ_list,
    cumulative_learning_nested NE τ N = List.foldr (max) 0 (τ_list.map (fun t => cumulative_learning_nested NE t N))
    ∨ fades τ :=
begin
  intros τ hτ,
  induction NE with E children ih,
  { apply trend_lifecycle_multi_spike E τ_list N h_nonempty, exact hτ },
  { let max_learn := List.foldr (max) 0 (τ_list.map (fun t => cumulative_learning_nested (node E children) t N)),
    by_cases h_dom : cumulative_learning_nested (node E children) τ N = max_learn,
    { left, exact h_dom },
    { right,
      have lt_max : cumulative_learning_nested (node E children) τ N < max_learn := sorry,
      exact suppressed_trajectory_fades E τ_list τ hτ lt_max } }
end
