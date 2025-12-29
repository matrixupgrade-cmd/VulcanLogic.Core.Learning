/-!
===============================================================================
EpistemicGradients.lean — Sobolev-style Gradients for Probabilistic Attractor Hierarchies
===============================================================================
Author: Sean Timothy
Date: 2025-12-29
Purpose:
  Extend EpistemicVeil.lean with gradient-like operators on the probabilistic
  flow layer for finite-state, non-deterministic hierarchies.
  This sets the stage for sensitivity analysis / Sobolev-style reasoning.
===============================================================================
-/

import Mathlib.Probability.ProbabilityMassFunction
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Real.Basic
import EpistemicVeil

open Finset ProbabilityMassFunction Real

variable {State : Type*} [Fintype State] [DecidableEq State] [Nonempty State]

-------------------------------------------------------------------------------
-- 0. Local gradient on PMF transitions
-------------------------------------------------------------------------------

/-- Local difference operator between two states in a probabilistic substrate -/
def local_gradient (P : ProbSubstrate State) (x y : State) : ℝ :=
  let px := P.transition x
  let py := P.transition y
  ∑ z in univ, |pmf.prob px z - pmf.prob py z|

/-- Normed gradient of expected reach probability wrt attractor -/
def reach_gradient (P : ProbSubstrate State) (steps : ℕ) (x : State)
    (A : AttractorSpace (crisp_version P)) : ℝ :=
  ∑ y in A.carrier, |expected_reach_prob P steps x y - expected_reach_prob P steps x y|

-------------------------------------------------------------------------------
-- 1. Sobolev-style semi-norm (L2 variant)
-------------------------------------------------------------------------------

/-- L2 semi-norm across substrate states for a probabilistic layer -/
def L2_sobolev_norm (P : ProbSubstrate State) (steps : ℕ)
    (A : AttractorSpace (crisp_version P)) : ℝ :=
  sqrt (∑ x in univ, (reach_gradient P steps x A)^2)

-------------------------------------------------------------------------------
-- 2. Gradient propagation through nested hierarchy
-------------------------------------------------------------------------------

/-- Gradient at level n+1 from level n */
def hierarchy_gradient (P : ProbSubstrate State) (n : ℕ)
    (A : NestedAttractor base_S (n+1)) : ℝ :=
  ∑ B in univ.filter (fun B : NestedAttractor base_S n => IsProbNested A B),
    L2_sobolev_norm P 1000 B.carrier  -- weighted sum over lower nested attractors

-------------------------------------------------------------------------------
-- 3. Sensitivity / perturbation operator
-------------------------------------------------------------------------------

/-- Small perturbation δ on transition probabilities, linearized effect */
def perturbation_effect (P : ProbSubstrate State) (δ : State → State → ℝ)
    (x : State) (A : AttractorSpace (crisp_version P)) : ℝ :=
  ∑ y in univ, δ x y * expected_reach_prob P 1000 x y

/-!
Interpretation / next steps:

• `local_gradient` → measures sensitivity between two probabilistic state transitions.
• `reach_gradient` → expected change in reach probability wrt attractor.
• `L2_sobolev_norm` → Sobolev-style semi-norm for finite-state system.
• `hierarchy_gradient` → propagates sensitivity across nested attractor levels.
• `perturbation_effect` → linearized estimate of how small transition changes affect reach probabilities.

This gives a constructive, Lean-ready layer for superconductor-style gradient analysis
on top of the probabilistic epistemic veil.

Next: prove boundedness, monotonicity, and convergence of these norms, 
or link to sampling-based empirical estimates for finite-observer approximations. 🌌
-/
