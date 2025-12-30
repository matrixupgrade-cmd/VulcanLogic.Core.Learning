/-!
===============================================================================
Influential Trajectories with Learning Capacity in Local Self-Attractor Ecologies
===============================================================================

Author: Sean Timothy
Date: 2025

Purpose:
  Sketch of conditional existence theorem for influential trajectories
  that carry capacity to induce learning in finite dynamical systems.

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

variable (Time : Type) [LinearOrder Time] [OrderBot Time]
variable (State : Type) [Fintype State] [DecidableEq State]
variable (Signal : Type)
variable (Operator : Type)

-- Operator dynamics
variable (step : Operator → State → Signal → State)
variable (input : Time → Signal)

-------------------------------------------------------------------------------
-- 1. Trajectories
-------------------------------------------------------------------------------

def Trajectory := Time → State

-------------------------------------------------------------------------------
-- 2. Asymmetry / State salience
-------------------------------------------------------------------------------

variable (weight : State → ℝ)
axiom weight_pos : ∀ s, 0 < weight s
axiom weight_varied : ∃ s₁ s₂, weight s₁ ≠ weight s₂

-------------------------------------------------------------------------------
-- 3. Decay (fading)
-------------------------------------------------------------------------------

variable (decay : Time → ℝ)
axiom decay_nonneg : ∀ t, 0 ≤ decay t
axiom decay_tends_to_zero : Tendsto decay atTop (𝓝 0)

def activation (τ : Trajectory Time State) (t : Time) : ℝ :=
  decay t * weight (τ t)

def fades (τ : Trajectory Time State) : Prop :=
  ∀ ε > 0, ∃ T, ∀ t ≥ T, activation Time State weight decay τ t < ε

-------------------------------------------------------------------------------
-- 4. Local self-attractor ecology
-------------------------------------------------------------------------------

variable (Ecology : Type)
variable (is_self_attractor_ecology : Operator → Ecology → Prop)

-- Reachability / influence without formal topology
def influences_local_ecology (τ : Trajectory Time State) (op : Operator) (E : Ecology) : Prop :=
  ∃ t, τ t ∈ basin_of E  -- placeholder for basin membership

-------------------------------------------------------------------------------
-- 5. Learning capacity induced by a trajectory
-------------------------------------------------------------------------------

-- Abstract notion of learning: trajectory changes state weights / distribution in E
def induces_learning (τ : Trajectory Time State) (E : Ecology) : Prop :=
  ∃ s ∈ E, ∃ t, change_in_weight s (τ t) ≠ 0

-- Influential trajectory: affects local ecology and induces learning
def influential_trajectory (τ : Trajectory Time State) (op : Operator) (E : Ecology) : Prop :=
  influences_local_ecology τ op E ∧ induces_learning τ E

-------------------------------------------------------------------------------
-- 6. Conditional existence theorem (sketch)
-------------------------------------------------------------------------------

/--
Conditional existence:

If a local self-attractor ecology exists for an operator,
then there exists a trajectory τ that either:

  1. is influential (affects the local ecology and induces learning), or
  2. fades

Proof pressure points:

  • Existence of τ that enters basin of some attractor in E
  • Ensuring τ actually induces change (learning capacity)
  • Decay must be sufficient for fading if trajectory does not integrate
  • Finite state and asymmetry (weight_varied) required for constructive spike
-/
theorem exists_influential_trajectory :
  ∀ (op : Operator) (E : Ecology),
    is_self_attractor_ecology op E →
      ∃ τ : Trajectory Time State,
        influential_trajectory τ op E ∨ fades Time State weight decay τ :=
by
  -- Sketch proof steps:
  --
  -- 1. Assume local ecology exists
  -- 2. Construct candidate trajectory τ (spike at some state/time or guided by input)
  -- 3. If τ enters basin and modifies state weights → influential_trajectory
  -- 4. Else, τ fades via decay lemma
  --
  -- Each step is a proof pressure point for Lean.
  admit

-------------------------------------------------------------------------------
-- 7. Notes
-------------------------------------------------------------------------------

/-!
• Conditional: avoids operators that cannot support local ecology.
• Local / nested: influence and learning are defined in terms of reachable sub-ecologies.
• Influential trajectory captures potential for learning; fade captures transient influence.
• Proof pressure points explicitly annotated above.
• Future work:
    - Define `basin_of` and `change_in_weight` formally
    - Construct witness trajectories under strengthened assumptions
    - Investigate nested / meta-ecology influence chains
-/
