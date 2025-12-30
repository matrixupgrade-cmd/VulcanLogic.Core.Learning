/-!
===============================================================================
Transient Trajectories in Finite Attractor Ecologies
===============================================================================

Author: Sean Hitch
Date: 2025

Status:
  Master sketch / conjectural existence theorem.

Intent:
  Test whether finite signal-coupled dynamical systems with decay and asymmetry
  *can* (or must) admit trajectories that are:

    • temporarily dominant
    • non-attracting (fade)
    • ecology-altering

Failure is informative.
No phenomenology. No intelligence claims.

===============================================================================
-/

import Mathlib

-------------------------------------------------------------------------------
-- 0. Time and State
-------------------------------------------------------------------------------

variable (Time : Type)
variable [LinearOrder Time] [OrderBot Time]

-- Finite substrate
variable (State : Type)
variable [Fintype State] [DecidableEq State]

-------------------------------------------------------------------------------
-- 1. Signals and Dynamics
-------------------------------------------------------------------------------

variable (Signal : Type)

-- Base dynamics
variable (step : State → Signal → State)

-- External input stream
variable (input : Time → Signal)

-------------------------------------------------------------------------------
-- 2. Trajectories
-------------------------------------------------------------------------------

def Trajectory := Time → State

-------------------------------------------------------------------------------
-- 3. Asymmetry / Salience
-------------------------------------------------------------------------------

-- Intrinsic salience / cost / richness of states
variable (weight : State → ℝ)
axiom weight_pos : ∀ s, 0 < weight s
axiom weight_varied : ∃ s₁ s₂, weight s₁ ≠ weight s₂

-------------------------------------------------------------------------------
-- 4. Decay (bounded attention / novelty)
-------------------------------------------------------------------------------

variable (decay : Time → ℝ)
axiom decay_nonneg : ∀ t, 0 ≤ decay t
axiom decay_tends_to_zero : Tendsto decay atTop (𝓝 0)

-------------------------------------------------------------------------------
-- 5. Activation and dominance
-------------------------------------------------------------------------------

-- Time-local activation of a trajectory
def activation (τ : Trajectory Time State) (t : Time) : ℝ :=
  decay t * weight (τ t)

-- Relative, local dominance (no attractor assumptions)
def dominant_at (τ : Trajectory Time State) (t : Time) : Prop :=
  ∀ τ' : Trajectory Time State,
    activation Time State weight decay τ t
      ≥ activation Time State weight decay τ' t

-------------------------------------------------------------------------------
-- 6. Fading (non-attractor)
-------------------------------------------------------------------------------

-- Trajectory eventually falls below any salience threshold
def fades (τ : Trajectory Time State) : Prop :=
  ∀ ε > 0, ∃ T, ∀ t ≥ T,
    activation Time State weight decay τ t < ε

-------------------------------------------------------------------------------
-- 7. Ecology and deformation
-------------------------------------------------------------------------------

-- Abstract ecology = bias / structural weighting
def Ecology := State → ℝ
variable (eco : Ecology State)

-- Ecology-sensitive dynamics (weak dependence only)
variable (step_eco : Ecology State → State → Signal → State)

-- Minimal distinguishability: different ecologies can eventually matter
axiom eco_sensitive :
  ∀ eco eco' : Ecology State, eco ≠ eco' →
    ∃ s sig, step_eco eco s sig ≠ step_eco eco' s sig

-- Trajectory deforms ecology if it induces a persistent change
def deforms_ecology (τ : Trajectory Time State) : Prop :=
  ∃ eco' : Ecology State,
    eco' ≠ eco ∧
    ∃ T, ∀ t ≥ T, ∃ sig,
      step_eco eco (τ t) sig ≠ step_eco eco' (τ t) sig

-------------------------------------------------------------------------------
-- 8. Main conjecture: existence of transient influential trajectory
-------------------------------------------------------------------------------

/--
Open Conjecture:

Under finite state, asymmetry, decay, and ecology-sensitive dynamics,
there exists a trajectory that is:

  • dominant at some time
  • fading (non-attracting)
  • ecology-deforming

Truth value unknown.
Failure yields structural obstruction.
-/
theorem exists_transient_influential_trajectory :
  ∃ τ : Trajectory Time State,
    (∃ t, dominant_at Time State weight decay τ t) ∧
    fades Time State weight decay τ ∧
    deforms_ecology Time State Signal step_eco eco τ :=
by
  -- Expected proof pressure points:
  --
  -- 1. Finite State + weight_varied ⇒ possibility of local dominance
  -- 2. Input novelty ⇒ dominance can be realized at some time
  -- 3. decay_tends_to_zero ⇒ dominance cannot persist
  -- 4. Ecology sensitivity + persistence ⇒ deformation possible
  --
  -- Any failure here is a real obstruction theorem.
  admit

-------------------------------------------------------------------------------
-- 9. Interpretation notes (non-formal)
-------------------------------------------------------------------------------

/-!
• This file does NOT assert inevitability.
• It asserts that inevitability is a meaningful question.
• "Trend", "attention", "assembly", "consciousness" are interpretations,
  not formal objects.

If this conjecture is false, the counterexample will teach us something deep.
-/
