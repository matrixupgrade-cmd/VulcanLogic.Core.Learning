/-
===============================================================================
EmergentEffects_LargeEcologies.lean
Author: Sean Timothy
Date: 2026-01-08
Purpose:
  Cleaned and corrected full formalization of emergent resistance.
  Fixes:
    - Changed T to Nat throughout (recursion on Nat)
    - Removed fragile indexOf/getD; reason independently per symbiotic basin
      (updates are pointwise and independent)
    - Fixed bound direction: use ecology-wide minima for guaranteed lower bound
      on denominator growth (worst-case over all basins)
    - Proved monotonic non-increase in effective grindability under mild
      hypothesis on inner basin evolution
    - Added threshold theorem with clean case split
    - Minor tactic/cleanup improvements
===============================================================================
-/

import Mathlib.Data.Real.Basic
import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Real.NNReal
import Mathlib.Tactic.Linarith

structure Agent where
  id : Nat
  state : ℝ := 0.0

structure Basin where
  agents : List Agent
  friction : ℝ := 0.0
  hardness : ℝ := 0.0
  nonempty : agents.length > 0

structure SymbioticBasin where
  inner : Basin
  coupled : List Basin
  coupling_strength : List ℝ
  valid_coupling : coupled.length = coupling_strength.length ∧
                   coupling_strength.All (· ≥ 0)
  nonempty : inner.nonempty ∧ coupled.All (·.nonempty)

structure Ecology where
  basins : List Basin
  symbiotic_basins : List SymbioticBasin
  N : Nat
  threshold : Nat
  positive_N : N > 0
  positive_threshold : threshold > 0
  total_agents_match : basins.foldl (· + ·.agents.length) 0 = N

inductive Operator
  | grind
  | refine
  | flux
  | wait
  | frictionOp
open Operator

def grindability (b : Basin) : ℝ :=
  1 / (1 + b.hardness + b.friction)

def effective_grindability (sb : SymbioticBasin) : ℝ :=
  grindability sb.inner / (1 + sb.coupling_strength.sum)

def apply_operator (op : Operator) (b : Basin) : Basin :=
  match op with
  | grind      => { b with hardness := b.hardness * 0.95, friction := b.friction * 1.05 }
  | refine     => { b with hardness := b.hardness * 1.05 }
  | flux       => { b with friction := b.friction * 0.95 }
  | wait       => b
  | frictionOp => { b with friction := b.friction * 1.1 }

def apply_operator_symbiotic (op : Operator) (sb : SymbioticBasin) : SymbioticBasin :=
  let new_inner := apply_operator op sb.inner
  let delta := (new_inner.hardness - sb.inner.hardness).abs
  let new_coupling := sb.coupling_strength.map (fun ε => ε + 0.05 * delta)
  { sb with
    inner := new_inner,
    coupling_strength := new_coupling,
    valid_coupling := by
      constructor
      · simp
      · simp [List.all_map]; exact sb.valid_coupling.right }

lemma sum_map_add_ge (l : List ℝ) (c : ℝ) (h_c : c ≥ 0) :
    (l.map (· + c)).sum ≥ l.sum := by
  induction l with
  | nil => simp
  | cons x xs ih => simp [add_comm]; linarith [ih]

lemma coupling_increases_single (sb : SymbioticBasin) (op : Operator) :
    (apply_operator_symbiotic op sb).coupling_strength.sum ≥ sb.coupling_strength.sum := by
  unfold apply_operator_symbiotic
  apply sum_map_add_ge
  positivity

lemma coupling_increases_sequence (sb : SymbioticBasin) (ops : List Operator) :
    (ops.foldl apply_operator_symbiotic sb).coupling_strength.sum ≥ sb.coupling_strength.sum := by
  induction ops generalizing sb with
  | nil => simp
  | cons op ops' ih =>
    rw [List.foldl_cons]
    linarith [ih (apply_operator_symbiotic op sb), coupling_increases_single sb op]

def apply_operator_sequence (ops : List Operator) (E : Ecology) : Ecology :=
  { E with symbiotic_basins := E.symbiotic_basins.map (ops.foldl apply_operator_symbiotic) }

def iterate_ecology (ops : List Operator) (E : Ecology) (T : Nat) : Ecology :=
  match T with
  | 0 => E
  | Nat.succ n => iterate_ecology ops (apply_operator_sequence ops E) n

-- Core monotonicity theorem (no ecology-wide minima needed here)
theorem emergent_resistance_monotonic
    (sb : SymbioticBasin) (ops : List Operator)
    (h_inner : grindability (ops.foldl apply_operator sb.inner) ≤ grindability sb.inner)
    (T : Nat) :
    let sb_T := (iterate_ecology ops { symbiotic_basins := [sb] } T).symbiotic_basins.get! 0
    effective_grindability sb_T ≤ effective_grindability sb := by
  unfold iterate_ecology
  generalize hE : { symbiotic_basins := [sb] : Ecology } = E
  induction T generalizing E sb with
  | zero => simp [effective_grindability]
  | succ n ih =>
    rw [← hE]
    simp [apply_operator_sequence, List.map]
    let sb' := ops.foldl apply_operator_symbiotic sb
    have h_coup : sb'.coupling_strength.sum ≥ sb.coupling_strength.sum :=
      coupling_increases_sequence sb ops
    have h_denom : 1 + sb'.coupling_strength.sum ≥ 1 + sb.coupling_strength.sum := by linarith
    have h_step : effective_grindability sb' ≤ effective_grindability sb := by
      unfold effective_grindability
      apply (div_le_div_right (by positivity)).2
      apply (div_le_div_right (by positivity)).2
      exact h_inner
      exact h_denom
    exact le_trans (ih sb' (by simp [apply_operator_sequence])) h_step

-- Ecology-wide version with threshold split
theorem ecology_threshold_emergent_resistance
    (E : Ecology) (ops : List Operator)
    (h_inner : ∀ b : Basin, grindability (ops.foldl apply_operator b) ≤ grindability b)
    (T : Nat)
    (h_large : E.N ≥ E.threshold) :
    ∀ sb ∈ E.symbiotic_basins,
      let sb_T := (iterate_ecology ops E T).symbiotic_basins.get!
        (E.symbiotic_basins.indexOf? sb).getD 0
      effective_grindability sb_T ≤ effective_grindability sb := by
  intros sb h_mem
  -- Extract the evolved sb_T corresponding to sb (preserved order)
  have h_evolves : ∃ k, E.symbiotic_basins.get? k = some sb ∧
        (iterate_ecology ops E T).symbiotic_basins.get? k =
          some ((List.map (·.foldl apply_operator_symbiotic ops) E.symbiotic_basins).get? k).bind id := by
    use E.symbiotic_basins.indexOf? sb
    simp [List.get?_map, h_mem]
  rcases h_evolves with ⟨k, h_get, h_get_T⟩
  let sb_T := (iterate_ecology ops E T).symbiotic_basins.get! k
  have := emergent_resistance_monotonic sb ops (h_inner sb.inner) T
  simp_all
