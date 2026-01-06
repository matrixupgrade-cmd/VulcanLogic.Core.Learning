/-!
===============================================================================
MonotonePersistence.lean
===============================================================================

Author: Sean Timothy
Date: 2026-01-06

Purpose:
  Capstone principle: local monotonicity of an evaluative measure
  implies global persistence along a trajectory.

  Unifies MonkPath, CompressionPlaybook, Flux preservation,
  Alfheim bounds, ROI-style ledgers, and related agent systems.

  This file isolates the logic core:
  persistence arises from order + agency, not specific dynamics.
===============================================================================
-/

import Mathlib.Order.Basic
import Mathlib.Data.Nat.Basic

variable {State Action Measure : Type*}
variable [Preorder Measure]

/-- State transition induced by an action. -/
variable (step : State → Action → State)

/-- Evaluative measure (currency / ledger) on states. -/
variable (eval : State → Measure)

/-- Agent policy: chooses an action from the current state. -/
variable (policy : State → Action)

/-- Local monotonicity:
    the chosen action never decreases the measure. -/
def MonotoneAt (s : State) : Prop :=
  eval (step s (policy s)) ≥ eval s

/-- Iterated trajectory starting from an initial state `s₀`. -/
def trajectory (s₀ : State) : ℕ → State
  | 0     => s₀
  | n + 1 => step (trajectory s₀ n) (policy (trajectory s₀ n))

/-- Global persistence:
    the measure is non-decreasing along the trajectory. -/
def Persistent (s₀ : State) : Prop :=
  ∀ n,
    eval (trajectory step policy s₀ (n + 1))
      ≥ eval (trajectory step policy s₀ n)

/-- Capstone theorem:
    local monotonicity implies global persistence. -/
theorem monotone_implies_persistent
  (h_mono : ∀ s, MonotoneAt step eval policy s)
  (s₀ : State) :
  Persistent step policy s₀ :=
by
  intro n
  -- unfold one step of the trajectory
  simp [Persistent, trajectory]
  -- exactly the local monotonicity condition
  apply h_mono

/-!
===============================================================================
Optional extensions (sketches only — not part of the logic core)
===============================================================================

These statements are intentionally *not* proven here.
They belong in system-specific files (e.g. MonkPath, CompressionPlaybook).

They are included to document how stronger guarantees arise
when additional structure is supplied.
===============================================================================
-/

/-- Strict local increase of the measure. -/
def StrictlyMonotoneAt (s : State) : Prop :=
  eval (step s (policy s)) > eval s

/-- Eventual stabilization of the trajectory. -/
def EventuallyStabilizes (s₀ : State) : Prop :=
  ∃ N, ∀ m ≥ N,
    trajectory step policy s₀ (m + 1)
      = trajectory step policy s₀ m

/-- Sketch theorem (interface only):

If:
  • the state space is finite,
  • the measure is well-founded,
  • the policy strictly increases the measure whenever possible,

Then:
  • the trajectory must eventually stabilize.

Concrete proofs live in specialized files.
-/
theorem strict_monotone_finite_implies_stabilization :
  True :=
by
  trivial

/-!
===============================================================================
Summary

• This file isolates the minimal logical structure required for agent persistence.
• All further dynamics supply concrete instances of the evaluative measure.
• Persistence is bookkeeping (order + agency), not dynamics.
===============================================================================
-/
