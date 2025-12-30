import Mathlib.Data.Real.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.List.Basic
import Mathlib.Analysis.Asymptotics.Asymptotics

open Finset List

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

structure Ecology where
  name : String
  states : Finset State
  basin  : State → Prop
  weight_update : State → ℝ → State → ℝ
  learning_nontrivial : ∀ (s ∈ states) (infl > 0), weight_update s infl s ≠ weight s
  interactions : List (Ecology × ℕ)

def influences_local_ecology (E : Ecology) (τ : Trajectory) : Prop := ∃ t, τ t ∈ E.states

def delayed_τ (τ : Trajectory) (d : ℕ) : Trajectory := fun k => τ (k + d)

def cumulative_learning (E : Ecology) (τ : Trajectory) : ℝ :=
  let local := List.sum (List.map (activation τ) (List.range 100))
  let nested := List.sum (E.interactions.map (fun (E', d) => cumulative_learning E' (delayed_τ τ d)))
  local + nested

def induces_learning (E : Ecology) (τ : Trajectory) : Prop :=
  let infl := cumulative_learning E τ
  infl > 0 ∧ ∃ s ∈ E.states, E.weight_update s infl s ≠ weight s

def influential_trajectory (E : Ecology) (τ : Trajectory) : Prop :=
  influences_local_ecology E τ ∧ induces_learning E τ

def τ_multi_spike (spikes : List (ℕ × State)) : Trajectory :=
  fun t =>
    match spikes.filter (fun p => p.1 = t) with
    | [] => default
    | (_, s) :: _ => s

inductive NestedEcology
| leaf : Ecology → NestedEcology
| node : Ecology → List NestedEcology → NestedEcology

open NestedEcology

def cumulative_learning_nested (N : ℕ) : NestedEcology → Trajectory → ℝ
| leaf E, τ => List.sum (List.map (activation τ) (List.range N))
| node E children, τ =>
  let local := List.sum (List.map (activation τ) (List.range N))
  let nested := List.sum (children.map (fun child => cumulative_learning_nested N child (delayed_τ τ 1)))
  local + nested

def influential_nested (NE : NestedEcology) (τ : Trajectory) (N : ℕ) : Prop :=
  cumulative_learning_nested N NE τ > 0

def compose_ecologies (E1 E2 : Ecology) (delay : ℕ) : Ecology :=
{ name := E1.name ++ "+" ++ E2.name,
  states := E1.states ∪ E2.states,
  basin := fun s => E1.basin s ∨ E2.basin s,
  weight_update := fun s infl s' =>
    if h1 : s ∈ E1.states then E1.weight_update s infl s'
    else if h2 : s ∈ E2.states then E2.weight_update s infl s'
    else weight s',
  learning_nontrivial := by
    intros s hs infl hpos
    cases hs with
    | inl h1 => exact E1.learning_nontrivial s h1 infl hpos
    | inr h2 => exact E2.learning_nontrivial s h2 infl hpos,
  interactions := E1.interactions ++ E2.interactions.map (fun (E', d) => (E', d + delay)) }

lemma composed_ecology_influential
  (E1 E2 : Ecology)
  (τ : Trajectory)
  (delay : ℕ)
  (h1 : influential_trajectory E1 τ)
  (h2 : influential_trajectory E2 (delayed_τ τ delay)) :
  influential_trajectory (compose_ecologies E1 E2 delay) τ := by
  unfold influential_trajectory
  constructor
  · obtain ⟨t, ht⟩ := h1.left
    use t
    simp [compose_ecologies, ht]
  · unfold induces_learning
    have pos_local : cumulative_learning E1 τ > 0 := h1.right.left
    have pos_nested : cumulative_learning E2 (delayed_τ τ delay) > 0 := h2.right.left
    have total_pos : cumulative_learning (compose_ecologies E1 E2 delay) τ > 0 := by
      simp [cumulative_learning, compose_ecologies, pos_local, pos_nested]
      linarith
    obtain ⟨s, hs, hchange⟩ := h1.right.right
    use s, hs
    simp [compose_ecologies, hs, hchange]
    exact total_pos

def max_learning_nested (NE : NestedEcology) (τ_list : List Trajectory) (N : ℕ) : ℝ :=
  List.foldr max 0 (τ_list.map (cumulative_learning_nested N NE))

def dominant_nested_trajectories (NE : NestedEcology) (τ_list : List Trajectory) (N : ℕ) : List Trajectory :=
  τ_list.filter (fun τ => cumulative_learning_nested N NE τ = max_learning_nested NE τ_list N)

def meta_learning_capacity_nested (NE : NestedEcology) (τ_list : List Trajectory) (N : ℕ) : ℝ :=
  List.sum (dominant_nested_trajectories NE τ_list N).map (cumulative_learning_nested N NE)

lemma meta_learning_capacity_nested_nonneg
  (NE : NestedEcology) (τ_list : List Trajectory) (N : ℕ) :
  0 ≤ meta_learning_capacity_nested NE τ_list N := by
  unfold meta_learning_capacity_nested
  apply sum_nonneg
  intro _ _
  apply sum_nonneg
  intro _ _
  apply mul_nonneg (decay_nonneg _) (by linarith [weight_pos _])

lemma suppressed_trajectory_fades
  (E : Ecology)
  (trajectories : List Trajectory)
  (τ : Trajectory)
  (hτ : τ ∈ trajectories)
  (h_sup : cumulative_learning E τ < List.foldr max 0 (trajectories.map (cumulative_learning E))) :
  fades τ := by
  intro ε ε_pos
  obtain ⟨T, hT⟩ := decay_tendsto_zero ε_pos
  use T
  intro t ht
  let w_max := Finset.sup univ weight
  have hw : ∀ s, weight s ≤ w_max := Finset.le_sup (mem_univ _)
  calc activation τ t
    = decay t * weight (τ t) := rfl
    _ ≤ decay t * w_max := mul_le_mul_of_nonneg_left (hw (τ t)) (decay_nonneg t)
    _ < ε := hT t ht

theorem nested_ecology_trend_lifecycle
  (NE : NestedEcology)
  (τ_list : List Trajectory)
  (N : ℕ)
  (h_nonempty : τ_list ≠ []) :
  ∀ τ ∈ τ_list,
    cumulative_learning_nested N NE τ = max_learning_nested NE τ_list N ∨ fades τ := by
  intro τ hτ
  by_cases h_dom : cumulative_learning_nested N NE τ = max_learning_nested NE τ_list N
  · left; exact h_dom
  · right
    have h_lt : cumulative_learning_nested N NE τ < max_learning_nested NE τ_list N := lt_of_le_of_ne (le_max_learning_nested _ _ _ hτ) h_dom.symm
    induction NE with
    | leaf E =>
      simp [cumulative_learning_nested] at h_lt
      simp [max_learning_nested, cumulative_learning] at h_lt
      exact suppressed_trajectory_fades E τ_list τ hτ h_lt
    | node E children ih =>
      simp [cumulative_learning_nested, max_learning_nested] at h_lt ⊢
      have local_lt : List.sum (List.map (activation τ) (List.range N)) < _ := by linarith
      exact suppressed_trajectory_fades E τ_list τ hτ local_lt
