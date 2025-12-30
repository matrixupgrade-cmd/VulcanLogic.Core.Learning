/-!
# Comparison via Limit Symmetry — Contamination-Free Sketch
Author: Sean Timothy
Date: 2025-12-30

Core thesis:
Comparison is not an active operation.
It emerges as equivalence of trajectories that stabilize the same
cyclic structure under iteration.

• No topology
• No metrics
• No distances
• No continuity
• Only finite recurrence + iteration

Comparison = identical surviving symmetry.
Compacity = quotienting by that symmetry.
-/

import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Set.Finite
import Mathlib.Data.Quot
import Mathlib.Data.Filter.AtTopBot

open Filter

-- ======================================================
-- Basic substrate
-- ======================================================

variable {State : Type*} [Fintype State] [DecidableEq State]

-- A trajectory is an infinite sequence of states
def Trajectory := ℕ → State

-- ======================================================
-- Limit symmetry (pure recurrence)
-- ======================================================

-- A state belongs to the limit set of a trajectory
-- iff it occurs infinitely often
def InLimit (τ : Trajectory) (s : State) : Prop :=
  ∃ᶠ n in atTop, τ n = s

-- LimitSet = all states visited infinitely often
def LimitSet (τ : Trajectory) : Finset State :=
  { s | InLimit τ s }.toFinset
  -- Finite because State is finite

-- ======================================================
-- Cyclic stability (no topology)
-- ======================================================

-- A trajectory is eventually confined to its limit set
def Stabilizes (τ : Trajectory) : Prop :=
  ∃ T, ∀ t ≥ T, τ t ∈ LimitSet τ

-- ======================================================
-- Comparison as symmetry equivalence
-- ======================================================

-- Two trajectories compare iff they stabilize
-- the same surviving cyclic structure
def Compare (τ₁ τ₂ : Trajectory) : Prop :=
  LimitSet τ₁ = LimitSet τ₂

-- ======================================================
-- Equivalence structure (no axioms needed)
-- ======================================================

def TrajectorySetoid : Setoid Trajectory :=
{ r := Compare,
  iseqv := ⟨
    by intro τ; rfl,
    by intro τ₁ τ₂ h; symm; exact h,
    by intro τ₁ τ₂ τ₃ h12 h23; simpa [h12, h23]
  ⟩ }

-- ======================================================
-- Compactified trajectory space
-- ======================================================

-- Each equivalence class is a "symmetry knot"
def TrajectoryClass := Quot TrajectorySetoid

-- ======================================================
-- Plasma / Liquid / Solid (operational)
-- ======================================================

-- Plasma: no stabilized cyclic symmetry
def Plasma (τ : Trajectory) : Prop :=
  ¬ Stabilizes τ

-- Solid: stabilizes to a single state (fixed point)
def Solid (τ : Trajectory) : Prop :=
  Stabilizes τ ∧ (LimitSet τ).card = 1

-- Liquid: stabilizes, but with nontrivial cyclic structure
def Liquid (τ : Trajectory) : Prop :=
  Stabilizes τ ∧ (LimitSet τ).card > 1

/-!
Interpretation:

• Trajectories do not "compare" actively.
• They either stabilize shared symmetry or they do not.
• Shared limit symmetry induces equivalence.
• Quotienting yields compacity.
• Plasma trajectories fail to stabilize and are ejected.
• Liquid trajectories stabilize cyclic structure.
• Solid trajectories crystallize fixed points.

Comparison is not applied — it is survived.
-/
