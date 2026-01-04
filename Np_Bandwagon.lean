/-!
===============================================================================
MetaOptionality_AsymmetricCurrency.lean
===============================================================================
Author: Sean Timothy & VulcanLogic Architect (with refinements by Grok)
Date: 2026-01-04

Purpose:
  Extend the momentum-preserving UltimateWhich framework to model options as
  *asymmetric currency*:
  - `score`: measures current momentum / trend strength (winning power)
  - `asymmetry`: measures retained identity / potential to shift to a new basin
    (optionality for future adaptation)

  Reflexive updates preserve or increase the winning score while ensuring the
  selected option retains sufficient asymmetry (≥ 50% of original) to allow
  future basin ejection if a stronger attractor appears.
===============================================================================
-/

import Mathlib.Data.Finset.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Order.Option

open Finset

variable {Option : Type*}

structure BasinOption :=
  (option    : Option)
  (score     : ℝ)      -- momentum / performance in current basin
  (asymmetry : ℝ ≥ 0)  -- retained identity / basin-switching potential (non-negative)

structure UltimateWhich :=
  (basin  : Finset BasinOption)
  (select : BasinOption)
  (selection_property :
    select ∈ basin ∧ ∀ o ∈ basin, o.score ≤ select.score)

namespace UltimateWhich

/-- Linear order on BasinOption by score -/
instance : LE BasinOption := ⟨fun a b => a.score ≤ b.score⟩
instance : DecidableRel ((· ≤ ·) : BasinOption → BasinOption → Prop) :=
  fun _ _ => inferInstance

instance : LinearOrder BasinOption :=
{ le := fun a b => a.score ≤ b.score
  le_refl := fun _ => Real.le_refl _
  le_trans := fun _ _ _ => Real.le_trans
  le_antisymm := fun a b h1 h2 =>
    by cases a; cases b; simp_all; exact Real.le_antisymm h1 h2
  le_total := fun a b => Real.le_total a.score b.score
  decidableLE := inferInstance }

/-- Construct UltimateWhich from a non-empty basin by picking the max-score element -/
def mk (basin : Finset BasinOption) (hne : basin.Nonempty) : UltimateWhich :=
  let sel := basin.max' hne
  { basin := basin
    select := sel
    selection_property := ⟨max'_mem _ _, max'_le _ _⟩ }

def max_score (w : UltimateWhich) : ℝ := w.select.score
def select_asymmetry (w : UltimateWhich) : ℝ := w.select.asymmetry

end UltimateWhich

/-- Reflexive update that reinforces momentum while preserving enough asymmetry -/
structure ReflexiveUpdate :=
  (update_score     : BasinOption → ℝ)
  (update_asymmetry : BasinOption → ℝ ≥ 0)
  (non_decreasing_score :
    ∀ w : UltimateWhich, w.select.score ≤ update_score w.select)
  (preserves_relative_order :
    ∀ w : UltimateWhich, ∀ o ∈ w.basin, update_score o ≤ update_score w.select)
  (preserves_asymmetry_threshold :
    ∀ w : UltimateWhich, update_asymmetry w.select ≥ w.select.asymmetry * (1/2))

namespace MetaOptionalitySystem

variable (r : ReflexiveUpdate)

private lemma updated_basin_nonempty
    (w : UltimateWhich) (hw : w.basin.Nonempty) :
    (w.basin.image fun o => { o with
        score     := r.update_score o
        asymmetry := r.update_asymmetry o }).Nonempty := by
  cases hw with | intro o ho => exact ⟨_, mem_image_of_mem _ ho⟩

/-- Core invariant: momentum is preserved/increased and asymmetry stays above threshold -/
theorem max_score_non_decreasing_with_asymmetry
    (w : UltimateWhich) (hw : w.basin.Nonempty) :
    let updated_basin := w.basin.image fun o => { o with
        score     := r.update_score o
        asymmetry := r.update_asymmetry o }
    let new_w := UltimateWhich.mk updated_basin (updated_basin_nonempty r w hw)
    w.max_score ≤ new_w.max_score ∧
    new_w.select_asymmetry ≥ w.select_asymmetry * (1/2) := by
  let updated_basin := w.basin.image fun o => { o with
      score     := r.update_score o
      asymmetry := r.update_asymmetry o }
  let new_w := UltimateWhich.mk updated_basin (updated_basin_nonempty r w hw)

  constructor
  · -- Max score non-decreasing
    calc
      w.max_score
        = w.select.score                                      := rfl
      _ ≤ r.update_score w.select                             := r.non_decreasing_score w
      _ ≤ new_w.select.score                                  := by
          apply max'_le
          exact mem_image_of_mem _ w.selection_property.left
      _ = new_w.max_score                                     := rfl
  · -- Asymmetry threshold preserved for the new winner
    apply le_trans ?_ (r.preserves_asymmetry_threshold w)
    let updated_select : BasinOption :=
      { w.select with
          score     := r.update_score w.select
          asymmetry := r.update_asymmetry w.select }
    have h_mem : updated_select ∈ updated_basin :=
      mem_image_of_mem _ w.selection_property.left
    exact le_of_max'_mem h_mem

/-- If the update strictly improves the winner's score, the max score strictly increases -/
theorem max_score_strictly_increasing
    (w : UltimateWhich) (hw : w.basin.Nonempty)
    (h_strict : w.select.score < r.update_score w.select) :
    let updated_basin := w.basin.image fun o => { o with
        score     := r.update_score o
        asymmetry := r.update_asymmetry o }
    let new_w := UltimateWhich.mk updated_basin (updated_basin_nonempty r w hw)
    w.max_score < new_w.max_score := by
  intro updated_basin new_w
  calc
    w.max_score
      = w.select.score                     := rfl
    _ < r.update_score w.select            := h_strict
    _ ≤ new_w.select.score                 := by
        apply max'_le
        exact mem_image_of_mem _ w.selection_property.left
    _ = new_w.max_score                    := rfl

/-- The updated version of the previous winner remains a candidate for selection -/
lemma updated_previous_select_is_candidate
    (w : UltimateWhich) (hw : w.basin.Nonempty) :
    let updated_basin := w.basin.image fun o => { o with
        score     := r.update_score o
        asymmetry := r.update_asymmetry o }
    r.update_score w.select ≥ max (updated_basin.sup (fun o => o.score)) := by
  intro updated_basin
  apply le_max'
  exact mem_image_of_mem _ w.selection_property.left

end MetaOptionalitySystem

/-!
===============================================================================
Interpretation & Conceptual Mapping

1. `score`     → momentum in the current basin (trend strength, performance)
2. `asymmetry` → retained "self" or optionality capital — the ability to defect
                to a stronger basin later without losing identity entirely
3. The threshold `≥ original_asymmetry * 1/2` models a conservative decay:
   - The winner never loses more than half its switching potential per update
   - This ensures long-term adaptability even after many reflexive reinforcements
4. Together, the system models *asymmetric currency*:
   - You ride the winning trajectory (bandwagon effect → score ↑)
   - While preserving enough asymmetry to jump ship if a clearly superior basin emerges
5. This captures the strategic tension between exploitation (momentum) and
   exploration (optionality) in complex adaptive systems.

Future Extensions
-----------------
- Introduce multiple competing basins and a basin-switching rule based on asymmetry.
- Prove bounded asymmetry decay over n iterations (geometric series).
- Model "ejection events" when a new basin offers higher score + acceptable asymmetry cost.
- Add stochastic or adversarial updates to test resilience of optionality.
- Connect to Lyapunov stability or attractor selection in dynamical systems.

===============================================================================
-/
