/-!
# Comparison via Basin Capture — Sketch
Author: Sean Timothy
Date: 2025-12-30

Core idea:
Comparison is not an active operation.
It emerges when trajectories are captured by common attractor basins.

• Symmetry → basin attraction
• Basin capture → trajectory convergence
• Convergence → equivalence (comparison)
• Equivalence → compacity (finite learning)

No topology assumed.
All structure emerges from iteration + decay.
-/

import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Quot

-- ======================================================
-- Basic substrate
-- ======================================================

variable {State : Type} [Fintype State] [DecidableEq State]
variable {Signal : Type} [Fintype Signal] [DecidableEq Signal]

def Trajectory := ℕ → State

variable (step : State → Signal → State)
variable (input : ℕ → Signal)

-- ======================================================
-- Attractors and basins
-- ======================================================

-- An attractor is defined operationally via basin capture
structure Attractor where
  carrier : Finset State
  invariant :
    ∀ s ∈ carrier,
      step s (input 0) ∈ carrier

-- Basin = trajectories that eventually remain in the attractor
def Basin (A : Attractor step input) (τ : Trajectory) : Prop :=
  ∃ T, ∀ t ≥ T, τ t ∈ A.carrier

-- ======================================================
-- Decay enforces asymmetry
-- ======================================================

variable (decay : ℕ → ℝ)
axiom decay_nonneg : ∀ t, 0 ≤ decay t
axiom decay_tendsto_zero : Tendsto decay atTop (nhds 0)

-- ======================================================
-- Comparison as basin equivalence
-- ======================================================

-- Two trajectories "compare" iff they are captured by the same basin
def Compare (A : Attractor step input)
  (τ₁ τ₂ : Trajectory) : Prop :=
  Basin step input A τ₁ ∧ Basin step input A τ₂

-- ======================================================
-- Induced equivalence on trajectories
-- ======================================================

def SameAttractor (τ₁ τ₂ : Trajectory) : Prop :=
  ∃ A : Attractor step input, Compare step input A τ₁ τ₂

axiom sameAttractor_refl  : Reflexive (SameAttractor step input)
axiom sameAttractor_symm  : Symmetric (SameAttractor step input)
axiom sameAttractor_trans : Transitive (SameAttractor step input)

def TrajectorySetoid : Setoid Trajectory :=
{ r := SameAttractor step input,
  iseqv := ⟨
    sameAttractor_refl step input,
    sameAttractor_symm step input,
    sameAttractor_trans step input
  ⟩ }

-- ======================================================
-- Compactified trajectory space
-- ======================================================

def TrajectoryClass := Quot (TrajectorySetoid step input)

-- ======================================================
-- Plasma, Liquid, Solid (operational)
-- ======================================================

def Plasma (τ : Trajectory) : Prop :=
  ∀ A : Attractor step input, ¬ Basin step input A τ

def Solid (τ : Trajectory) : Prop :=
  ∃! A : Attractor step input, Basin step input A τ

def Liquid (τ : Trajectory) : Prop :=
  ¬ Plasma step input τ ∧ ¬ Solid step input τ

/-!
Interpretation:

• Comparison = shared basin capture
• Basin capture induces equivalence on trajectories
• Quotienting by equivalence yields compacity
• Plasma trajectories fail to compare and are ejected
• Liquid trajectories partially compare and enrich ecology
• Solid trajectories fully compare and stabilize structure

Comparison is not applied — it is survived.
-/
