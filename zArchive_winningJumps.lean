/-!
===============================================================================
UltimateWhich_MultiBasinSimulation.lean
===============================================================================
Author: Sean Timothy & VulcanLogic Architect (refined by Grok)
Date: 2026-01-04

Purpose:
  Simulate adaptive multi-basin dynamics for asymmetric currency options.

  Key mechanics:
  - Within each basin: reflexive updates reinforce the current winner (momentum)
  - Between basins: the winning option of a basin may "eject" to a stronger basin
    if it has sufficient remaining asymmetry (optionality capital)
  - This models bandwagon + adaptive defection: exploit the current attractor
    while preserving the ability to jump to a better one
===============================================================================
-/

import Mathlib.Data.Finset.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.List.Basic
import Mathlib.Order.Max

open Finset List

variable {OptionID : Type} [DecidableEq OptionID] [BEq OptionID]

structure BasinOption :=
  (id        : OptionID)      -- unique identifier (e.g. String, Nat)
  (score     : ℝ)             -- momentum / performance
  (asymmetry : ℝ ≥ 0)         -- optionality capital (ability to switch basins)

structure Basin :=
  (options : Finset BasinOption)
  (nonempty : options.Nonempty)

structure UltimateWhich :=
  (basin  : Basin)
  (select : BasinOption)
  (is_max : select ∈ basin.options ∧ ∀ o ∈ basin.options, o.score ≤ select.score)

namespace UltimateWhich

/-- Construct the winning selection for a non-empty basin -/
def mk (b : Basin) : UltimateWhich :=
  let sel := b.options.max' b.nonempty
  { basin := b
    select := sel
    is_max := ⟨max'_mem _ _, max'_le _ _⟩ }

def max_score (w : UltimateWhich) : ℝ := w.select.score
def select_asymmetry (w : UltimateWhich) : ℝ := w.select.asymmetry

/-- Update a single basin using a reflexive momentum-preserving rule -/
def update (r : ReflexiveUpdate) (w : UltimateWhich) : UltimateWhich :=
  let updated_options := w.basin.options.image fun o =>
    { o with
        score     := r.update_score o
        asymmetry := r.update_asymmetry o }
  let new_basin : Basin :=
    ⟨updated_options, by cases w.basin.nonempty; exact ⟨_, mem_image_of_mem _ ‹_›⟩⟩
  mk new_basin

end UltimateWhich

/-- Reflexive update that preserves momentum and asymmetry threshold -/
structure ReflexiveUpdate :=
  (update_score     : BasinOption → ℝ)
  (update_asymmetry : BasinOption → ℝ ≥ 0)
  (non_decreasing_score :
    ∀ w : UltimateWhich, w.select.score ≤ update_score w.select)
  (preserves_relative_order :
    ∀ w : UltimateWhich, ∀ o ∈ w.basin.options, update_score o ≤ update_score w.select)
  (preserves_asymmetry :
    ∀ w : UltimateWhich, update_asymmetry w.select ≥ w.select.asymmetry * (1/2))

namespace MultiBasinSimulation

variables
  {r : ReflexiveUpdate}
  {asym_eject_threshold : ℝ := 0.5}   -- minimum asymmetry needed to eject

/-- Find if there exists a strictly stronger basin that the current winner can join -/
def find_stronger_basin
    (current : UltimateWhich)
    (others  : List UltimateWhich) :
    Option UltimateWhich :=
  others.find? fun other =>
    other.max_score > current.max_score ∧
    current.select_asymmetry ≥ asym_eject_threshold

/-- Perform one step of multi-basin dynamics:
    1. Reflexively update all basins (reinforce internal momentum)
    2. Allow winning options to eject to stronger basins if asymmetry allows
-/
def step (basins : List UltimateWhich) : List UltimateWhich :=
  -- Step 1: update all basins internally
  let updated := basins.map (UltimateWhich.update r)

  -- Step 2: check each basin for possible ejection of its winner
  updated.map fun w =>
    match find_stronger_basin w (updated.erase w) with
    | none => w  -- stay: no better basin available or insufficient asymmetry
    | some target =>
      -- Eject the winner to the target basin
      let new_target_basin_opts := insert w.select target.basin.options
      let new_target_basin : Basin :=
        ⟨new_target_basin_opts,
         by simp [new_target_basin_opts]; exact ⟨w.select, mem_insert_self _ _⟩⟩
      UltimateWhich.mk new_target_basin

/-- Full simulation: returns the history of basin states over iterations -/
def simulate
    (initial_basins : List UltimateWhich)
    (iterations : ℕ)
    : List (List UltimateWhich) :=
  Nat.recOn iterations
    [initial_basins]
    (fun _ hist => hist ++ [step hist.getLast!])

/-- Convenience: run simulation and get final state -/
def simulate_final (initial : List UltimateWhich) (n : ℕ) : List UltimateWhich :=
  (simulate initial n).getLast!

/-- Example reflexive update: slight boost to winner, decay asymmetry slowly -/
def example_update : ReflexiveUpdate :=
{ update_score := fun o => o.score + if h : o.score = (UltimateWhich.mk sorry).max_score then 0.1 else 0
  update_asymmetry := fun o => o.asymmetry * 0.9
  non_decreasing_score := sorry  -- would need proper proof in full development
  preserves_relative_order := sorry
  preserves_asymmetry := sorry }

end MultiBasinSimulation

/-!
===============================================================================
Interpretation & Dynamics

- Each basin competes via its current champion (`select`)
- Reflexive updates model trend-following: winners gain momentum, asymmetry decays
  slowly (committing to the trajectory but not fully)
- Ejection rule: only the current winner can defect, and only if it retains enough
  asymmetry (≥ threshold) and sees a clearly superior trajectory elsewhere
- This creates adaptive bandwagon behavior:
  → Exploit strong local attractor
  → Preserve optionality to jump when a global better one emerges

Future Extensions
-----------------
1. Full proofs for example_update satisfying ReflexiveUpdate properties
2. Track full migration history of individual options
3. Stochastic basin scores or adversarial disruptions
4. Convergence results: does the system settle into the globally strongest basin?
5. Parameter sweeps: how does ejection threshold affect speed of adaptation?

===============================================================================
-/
