/-!
===============================================================================
Influential Trajectories with Learning Capacity in Local Self-Attractor Ecologies
===============================================================================

Author: Sean Hitch
Date: 2025

Purpose:
  Conditional existence theorem and constructive sketch for influential trajectories
  that can induce learning in finite dynamical systems.

Key Concepts:
  • Influential trajectory: a trajectory that affects a local ecology
  • Learning capacity: trajectory induces change in state distribution / weights
  • Local ecology: subset of self-attractors connected via trajectories
  • Fade vs integration: trajectory either fades or integrates into the ecology

===============================================================================
-/

import Mathlib

-------------------------------------------------------------------------------
-- 0. Time, State, Operator
-------------------------------------------------------------------------------

variable {Time : Type} [LinearOrder Time] [OrderBot Time] [TopologicalSpace Time]
variable {State : Type} [Fintype State] [DecidableEq State]
variable {Signal : Type}
variable {Operator : Type}

-- Operator dynamics
variable (step : Operator → State → Signal → State)
variable (input : Time → Signal)

-- Trajectory
def Trajectory := Time → State

-------------------------------------------------------------------------------
-- 1. State asymmetry / salience
-------------------------------------------------------------------------------

variable (weight : State → ℝ)
axiom weight_pos : ∀ s, 0 < weight s
axiom weight_varied : ∃ s₁ s₂, weight s₁ ≠ weight s₂

-------------------------------------------------------------------------------
-- 2. Decay (fading)
-------------------------------------------------------------------------------

variable (decay : Time → ℝ)
axiom decay_nonneg : ∀ t, 0 ≤ decay t
axiom decay_pos_at_finite : ∀ t, 0 < decay t  -- strengthened for dominance
axiom decay_tends_to_zero : Tendsto decay atTop (𝓝 0)

def activation (τ : Trajectory) (t : Time) : ℝ :=
  decay t * weight (τ t)

def fades (τ : Trajectory) : Prop :=
  ∀ ε > 0, ∃ T, ∀ t ≥ T, activation τ t < ε

-------------------------------------------------------------------------------
-- 3. Local Self-Attractor Ecology
-------------------------------------------------------------------------------

structure Ecology where
  states : Finset State                  -- subset forming the ecology
  basin  : State → Prop                  -- basin predicate
  weight_update : State → ℝ → State → ℝ -- learning rule

variable (E : Ecology)

def in_basin (s : State) : Prop := s ∈ E.basin

-- Concrete self-attractor condition: operator stabilizes states in ecology
variable (is_self_attractor_ecology :
  ∀ op s ∈ E.states, ∃ s' ∈ E.states,
    ∀ sig, step op s sig = s')

-------------------------------------------------------------------------------
-- 4. Influence and Learning
-------------------------------------------------------------------------------

-- Trajectory enters the basin of the ecology
def influences_local_ecology (τ : Trajectory) (op : Operator) : Prop :=
  ∃ t, in_basin (τ t)

-- Learning induced by trajectory
def induces_learning (τ : Trajectory) : Prop :=
  let total_infl := ∑ t, activation τ t
  total_infl > 0 ∧
  ∃ s ∈ E.states, E.weight_update s total_infl s ≠ weight s

-- Influential trajectory
def influential_trajectory (τ : Trajectory) (op : Operator) : Prop :=
  influences_local_ecology τ op ∧ induces_learning τ

-------------------------------------------------------------------------------
-- 5. Conditional existence theorem (constructive sketch)
-------------------------------------------------------------------------------

theorem exists_influential_or_fading_trajectory
  (op : Operator)
  (h_eco : ∀ s ∈ E.states, ∃ s' ∈ E.states, ∀ sig, step op s sig = s') :
  ∃ τ : Trajectory,
    influential_trajectory step decay weight E τ op ∨ fades decay weight τ :=
by
  -- Proof sketch (constructive, inspired by Grok):
  --
  -- 1. Pick high-weight state in ecology
  obtain ⟨s_high, s_low⟩ := weight_varied
  obtain hs_high : s_high ∈ E.states := sorry  -- assume ecology non-empty
  obtain hs' : ∃ s' ∈ E.states, ∀ sig, step op s_high sig = s' := h_eco s_high hs_high

  -- 2. Pick spike time with positive decay
  obtain t_spike : Time := classical.some (OrderBot.bounded_below Time)
  have h_decay_pos : 0 < decay t_spike := decay_pos_at_finite t_spike

  -- 3. Construct candidate trajectory: spike at high-weight state, then follow dynamics
  let τ : Trajectory := fun t =>
    if t = t_spike
      then s_high
      else step op (τ (t - 1)) (input t) -- discrete-time recursive definition

  -- 4. Case 1: τ enters basin and accumulates influence → influential
  have enters_basin : ∃ t, in_basin (τ t) := ⟨t_spike, by simp [τ, in_basin, hs_high]⟩

  have positive_infl : ∑ t, activation τ t > 0 := 
    calc 0 < decay t_spike * weight s_high := mul_pos h_decay_pos (weight_pos s_high)
      _ ≤ ∑ t, activation τ t := by sorry  -- single-term lower bound

  have learning : ∃ s ∈ E.states, E.weight_update s (∑ t, activation τ t) s ≠ weight s := 
    ⟨s_high, hs_high, by sorry⟩

  have influential : influential_trajectory step decay weight E τ op :=
    ⟨enters_basin, positive_infl.and ⟨learning⟩⟩

  -- 5. Conclude: either influential or fades (fallback)
  left
  exact influential

  -- Alternative branch if learning trivial: use `fades decay weight τ`
  -- right; exact fades_from_decay decay_tends_to_zero weight_pos

  exact ⟨τ, Or.inl influential⟩

-------------------------------------------------------------------------------
-- 6. Notes
-------------------------------------------------------------------------------

/-!
• Conditional: avoids operators that cannot support local ecology
• Local / nested: influence and learning defined in terms of reachable sub-ecologies
• Influential trajectory captures potential for learning; fade captures transient influence
• Proof pressure points:
    - Non-empty ecology
    - Positive decay for dominance
    - Non-trivial weight_update
    - Finite or convergent sum for activation
• Future work:
    - Formalize `basin_of` and `weight_update`
    - Investigate nested / meta-ecology influence chains
    - Construct explicit witnesses under stronger assumptions
-/
