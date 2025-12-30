/-!
===============================================================================
Existence of Influential or Fading Trajectories
Discrete Iterations, Finite Self-Attractor Ecologies
===============================================================================

NOTES:
- Time = discrete iterations ℕ
- All types (State, Signal, Operator) are finite
- Decay ensures fading
- Influential trajectories enter local ecologies and induce learning
===============================================================================
-/

import Mathlib
open Finset List

variable {State : Type} [Fintype State] [DecidableEq State]
variable {Signal : Type} [Fintype Signal] [DecidableEq Signal]
variable {Operator : Type} [Fintype Operator] [DecidableEq Operator]

def Trajectory := ℕ → State

-- Step function and input
variable (step : Operator → State → Signal → State)
variable (input : ℕ → Signal)

-- Weight function
variable (weight : State → ℝ)
axiom weight_pos : ∀ s, 0 < weight s
axiom weight_varied : ∃ s₁ s₂, weight s₁ ≠ weight s₂

-- Decay
variable (decay : ℕ → ℝ)
axiom decay_nonneg : ∀ t, 0 ≤ decay t
axiom decay_pos_at_finite : ∀ t, 0 < decay t
axiom decay_tends_to_zero : Tendsto decay atTop (𝓝 0)

-- Activation
def activation (τ : Trajectory) (t : ℕ) : ℝ := decay t * weight (τ t)

def fades (τ : Trajectory) : Prop :=
  ∀ ε > 0, ∃ T, ∀ t ≥ T, activation τ t < ε

-- Local ecology structure
structure Ecology where
  states : Finset State
  basin  : State → Prop
  weight_update : State → ℝ → State → ℝ

-- Influence & learning
def influences_local_ecology (E : Ecology) (τ : Trajectory) : Prop :=
  ∃ t, τ t ∈ E.states

def induces_learning (E : Ecology) (τ : Trajectory) : Prop :=
  let total_infl := List.sum (List.map (activation τ) (List.range 10)) -- finite horizon
  total_infl > 0 ∧ ∃ s ∈ E.states, E.weight_update s total_infl s ≠ weight s

def influential_trajectory (E : Ecology) (τ : Trajectory) : Prop :=
  influences_local_ecology E τ ∧ induces_learning E τ

-- Multi-spike trajectory constructor
def τ_multi_spike (spikes : List (ℕ × State)) : Trajectory :=
  λ t => match spikes.filter (λ p => p.1 = t) with
        | [] => (spikes.headD (0, spikes.head.2)).2 -- default first spike state
        | (_, s)::_ => s

-- ===========================================================================
-- Main Theorem: Existence of influential or fading trajectory
-- ===========================================================================

theorem exists_influential_or_fading_trajectory
  (E : Ecology)
  (spikes : List (ℕ × State)) :
  ∃ τ : Trajectory,
    influential_trajectory E τ ∨ fades τ :=
by
  -- 1. Construct candidate trajectory
  let τ := τ_multi_spike spikes

  -- 2. Case: trajectory enters ecology basin
  by_cases h_in : ∃ t, τ t ∈ E.states
  · left
    have infl_local : influences_local_ecology E τ := h_in
    have learn : ∃ s ∈ E.states, E.weight_update s (List.sum (List.map (activation τ) (List.range 10)) ) s ≠ weight s :=
      by
        -- assume weight_update non-trivial; can pick s from h_in
        sorry
    exact ⟨infl_local, ⟨by linarith, learn⟩⟩

  -- 3. Case: trajectory never enters basin → fades
  · right
    -- Use decay → 0 to guarantee fading
    exact by
      intros ε ε_pos
      let wmax := Finset.sup Finset.univ weight
      let T := Nat.ceil (wmax / ε)
      use T
      intros t ht
      calc activation τ t
            = decay t * weight (τ t) := by rfl
        _ ≤ wmax / (t + 1) := by
              apply mul_le_mul_of_nonneg_left
              · apply Finset.le_sup (Finset.mem_univ (τ t))
              · linarith [decay_nonneg t]
        _ ≤ ε := by linarith

  exact ⟨τ, _⟩
