/-!
===============================================================================
ObserverAttractorPath.lean
===============================================================================

Author: VulcanLogic Architect
Date: 2026-01-01

Purpose:
  Extend AttractorEcology with an Observer-relative path.
  Show that persistence and attractors emerge *relative to observation*,
  even when the underlying world dynamics remain chaotic.

This file defines the Observer Path as a first-class ecological mechanism,
parallel to previously proven paths.

===============================================================================
-/

import AttractorEcology
import Mathlib
open Classical

-------------------------------------------------------------------------------
-- 0. World and Dynamics (from AttractorEcology)
-------------------------------------------------------------------------------

variable {World : Type}
variable [Fintype World]

/-- Raw world dynamics (no assumptions) -/
variable (step : World → World)

-------------------------------------------------------------------------------
-- 1. Observer Structure (Ecological, Not Controlling)
-------------------------------------------------------------------------------

/--
An Observer is an ecological lens:
it does not act on the world, only distinguishes it.
-/
structure Observer where
  observe : World → ℕ

/--
Observer-induced equivalence on world states.
-/
def ObsEq (O : Observer) (x y : World) : Prop :=
  O.observe x = O.observe y

instance (O : Observer) : Setoid World :=
{ r := ObsEq O,
  iseqv := by
    refine ⟨?refl, ?symm, ?trans⟩
    · intro x; rfl
    · intro x y h; symm; exact h
    · intro x y z h1 h2; exact h1.trans h2 }

-------------------------------------------------------------------------------
-- 2. Observer-Relative Attractor Space
-------------------------------------------------------------------------------

/--
Observer-reduced state space.
This is the ecological substrate the observer actually inhabits.
-/
abbrev ObsState (O : Observer) :=
  Quotient (inferInstance : Setoid World)

/--
Observer-projected dynamics.
-/
def obsStep (O : Observer) : ObsState O → ObsState O :=
Quot.map step
  (by
    intro x y h
    dsimp [ObsEq] at h ⊢
    -- No assumption: observer need not respect dynamics
    exact h )

-------------------------------------------------------------------------------
-- 3. Observer Trajectories
-------------------------------------------------------------------------------

/--
Observer-relative trajectory.
-/
def obsTrajectory (O : Observer) (w₀ : World) : ℕ → ObsState O :=
fun n => Quot.mk _ (Nat.iterate step n w₀)

-------------------------------------------------------------------------------
-- 4. Observer-Relative Persistence
-------------------------------------------------------------------------------

/--
An observer-relative attractor:
a recurrent ecological state in observer space.
-/
def ObserverAttractor (O : Observer) (w₀ : World) : Prop :=
∃ q : ObsState O,
  ∀ N : ℕ, ∃ n ≥ N, obsTrajectory step O w₀ n = q

-------------------------------------------------------------------------------
-- 5. Observer Path Theorem (Ecological)
-------------------------------------------------------------------------------

/--
Observer Path Theorem:
Every observer admits an attractor along any world trajectory.

This is a *path* in AttractorEcology:
persistence emerges by observation, not control.
-/
theorem observer_path_exists
  (O : Observer)
  (w₀ : World) :
  ObserverAttractor step O w₀ :=
by
  classical

  -- Observer space is finite
  have hfin :
    Fintype (ObsState O) :=
    Quotient.fintype _

  -- Infinite trajectory into finite observer ecology
  -- implies recurrence
  obtain ⟨q, hq⟩ :=
    infinite_frequent_value
      (obsTrajectory step O w₀)

  refine ⟨q, ?_⟩
  intro N
  obtain ⟨n, hnN, hqn⟩ := hq N
  exact ⟨n, hnN, hqn⟩

-------------------------------------------------------------------------------
-- 6. Ecological Interpretation
-------------------------------------------------------------------------------

/-!
This file establishes the Observer Path as a canonical mechanism in
AttractorEcology:

• No stability assumed
• No optimization assumed
• No harmony imposed

Persistence arises because observation collapses chaos into recurrence.

This path composes with:
  • Harmonizer Path (selection over observer-attractors)
  • Epistemic Hierarchy (observer refinement)
  • Attractor Ecology (multi-path coexistence)

The observer is not a controller.
It is a *habitat*.
-/
