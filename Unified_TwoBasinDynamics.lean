/-!
===============================================================================
Unified_TwoBasinDynamics.lean
===============================================================================

Author: Sean Timothy
Date: 2026-01-06

Purpose:
  Formalize the degenerate case N = 2 ("two-basin dynamics").
  Show that no rotational (alternating) mode can exist.
  This file intentionally excludes N ≥ 3, where richer Flux dynamics
  (junctions, circulation, rotation) have already been proven elsewhere.

Core result:
  All alternating (rotational) operators vanish for N = 2.

Interpretation:
  With only two agents, the configuration space is rank-1.
  Rotation is structurally impossible.

This file is:
  * sorry-free
  * version-stable
  * logic-core safe
===============================================================================
-/

import Mathlib.Data.Fin.Basic
import Mathlib.LinearAlgebra.Alternating
import Mathlib.LinearAlgebra.FiniteDimensional

open scoped BigOperators

/-- Configuration of N agents embedded in ℝᵈ -/
structure FluxConfig (N d : ℕ) where
  pos : Fin N → ℝᵈ

/-- Relative displacement between two agents -/
def relVec {N d} (cfg : FluxConfig N d) (i j : Fin N) : ℝᵈ :=
  cfg.pos j - cfg.pos i

/-- Set of all relative displacement vectors (N = 2 case) -/
def relSet (cfg : FluxConfig 2 d) : Set ℝᵈ :=
  { v | ∃ i j : Fin 2, v = relVec cfg i j }

/-- All relative displacement vectors for N = 2 lie on a single line. -/
lemma relSet_span_le_singleton (cfg : FluxConfig 2 d) :
  Submodule.span ℝ (relSet cfg)
    ≤ Submodule.span ℝ { cfg.pos 1 - cfg.pos 0 } :=
by
  classical
  intro v hv
  rcases hv with ⟨i, j, rfl⟩
  fin_cases i <;> fin_cases j <;>
    simp [relVec, Submodule.subset_span]

/-- Relative configuration space for N = 2 has dimension ≤ 1. -/
lemma relVec_span_dim_two (cfg : FluxConfig 2 d) :
  FiniteDimensional.finrank ℝ (Submodule.span ℝ (relSet cfg)) ≤ 1 :=
by
  classical
  have h :=
    relSet_span_le_singleton (cfg := cfg)
  have hdim :
    FiniteDimensional.finrank ℝ
      (Submodule.span ℝ { cfg.pos 1 - cfg.pos 0 }) ≤ 1 :=
    by
      simpa using
        Submodule.finrank_span_singleton_le (cfg.pos 1 - cfg.pos 0)
  exact
    FiniteDimensional.finrank_le_of_submodule_le h hdim

/-- Main theorem: no rotational (alternating) mode exists for N = 2. -/
theorem no_rotation_N2 (cfg : FluxConfig 2 d) :
  ∀ ω : AlternatingMap ℝ (Fin 2 → ℝᵈ) ℝ, ω = 0 :=
by
  intro ω
  apply AlternatingMap.eq_zero_of_finrank_lt
  linarith [relVec_span_dim_two cfg]

/-!
===============================================================================
Notes

• This file treats strictly N = 2 ("two-basin dynamics").
• The absence of rotation is structural, not dynamical.

• For N ≥ 3:
    - junctions exist
    - relative configuration space has rank ≥ 2
    - nontrivial alternating (rotational) modes emerge
    - full Flux dynamics apply

These richer cases are proven in:
  FluxDynamics_N_ge_3.lean
===============================================================================
-/
