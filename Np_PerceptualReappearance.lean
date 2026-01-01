/-!
===============================================================================
PerceptualReappearanceOracleFull.lean
===============================================================================

Author: Sean Timothy & VulcanLogic Architect
Date: 2026-01-01

Purpose:
  Full observer-based perceptual reappearance framework:
  - PerceptualReappearance: infinite recurrence of perceptual states
  - observer_blink_function: finite approximation of recurrence
  - observer_rank_function: assigns positive value to recurrent states
  - M_min oracle function: minimal detection step for infinitely recurring states
  - M_min_rank oracle: minimal step for guaranteed positive rank
  Encodes ecological knowledge without control or agency.
===============================================================================
-/

import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Quotient
import Mathlib.Logic.Function.Basic
import Mathlib.Data.Set.Infinite
import Mathlib.Data.Nat.Prime

open Set Function Finset Classical

-------------------------------------------------------------------------------
-- 0. Observer and Perceptual Equivalence
-------------------------------------------------------------------------------

variable {World : Type*} [Fintype World]

/-- Arbitrary (possibly chaotic) deterministic world dynamics -/
variable (step : World → World)

/-- Observer: a passive ecological lens. Distinguishes states without acting -/
structure Observer (World : Type*) :=
  (observe : World → ℕ)

/-- Perceptual equivalence: states indistinguishable to the observer -/
def ObsEq (O : Observer World) (x y : World) : Prop := O.observe x = O.observe y

instance (O : Observer World) : DecidableRel (ObsEq O) := fun x y => Nat.decEq (O.observe x) (O.observe y)

instance (O : Observer World) : Setoid World :=
{ r := ObsEq O,
  iseqv := { refl := by intro x; rfl,
             symm := by intro x y h; exact h.symm,
             trans := by intro x y z h₁ h₂; exact h₁.trans h₂ } }

/-- Finite perceptual states observed by O -/
abbrev ObsState (O : Observer World) := Quotient (ObsEq O)

instance (O : Observer World) : Fintype (ObsState O) := Quotient.fintype (inferInstance : Setoid World)
instance (O : Observer World) : DecidableEq (ObsState O) := Quotient.decEq _

/-- Observer-relative trajectory: sequence of perceived states -/
def obsTrajectory (O : Observer World) (w₀ : World) : ℕ → ObsState O :=
  fun n => Quot.mk _ (Nat.iterate step n w₀)

-------------------------------------------------------------------------------
-- 1. Perceptual Reappearance
-------------------------------------------------------------------------------

/-- A perceptual state that recurs infinitely often along the trajectory -/
def InfinitelyRecurrent (step : World → World) (O : Observer World) (w₀ : World) (q : ObsState O) : Prop :=
  { n : ℕ | obsTrajectory step O w₀ n = q }.Infinite

/-- The set of all perceptual states that reappear infinitely often -/
def PerceptualReappearingStates (step : World → World) (O : Observer World) (w₀ : World) : Set (ObsState O) :=
  { q | InfinitelyRecurrent step O w₀ q }

/-- Existence theorem: any finite perceptual habitat guarantees recurrence -/
theorem perceptual_reappearance_exists (step : World → World) (O : Observer World) (w₀ : World) :
    (PerceptualReappearingStates step O w₀).Nonempty :=
by
  let traj := obsTrajectory step O w₀
  obtain ⟨q, h_inf⟩ := Fintype.exists_infinite_fiber (f := traj)
  exact ⟨q, h_inf⟩

/-- Blink lemma: for any future N, some reappearing state occurs later -/
lemma perceptual_reappearance_blink (step : World → World) (O : Observer World) (w₀ : World) (N : ℕ) :
  ∃ n ≥ N, ∃ q ∈ PerceptualReappearingStates step O w₀,
    obsTrajectory step O w₀ n = q :=
by
  obtain ⟨q, hq⟩ := perceptual_reappearance_exists step O w₀
  let S := { n | obsTrajectory step O w₀ n = q }
  have hS : S.Infinite := hq
  obtain ⟨n, hnS, hnN⟩ := hS.exists_nat_ge N
  exact ⟨n, hnN, q, hq, hnS⟩

-------------------------------------------------------------------------------
-- 2. Observer Blink Function / Rank Function
-------------------------------------------------------------------------------

/-- Approximate count of occurrences of a perceptual state in first M steps -/
def PerceptualValue_count (M : ℕ) (step : World → World) (O : Observer World) (w₀ : World) (q : ObsState O) : ℕ :=
  (Finset.range M).filter (fun n => obsTrajectory step O w₀ n = q).card

/-- Observer blink function: positive value for infinitely recurring states -/
def observer_blink_function (M : ℕ) (step : World → World) (O : Observer World) (w₀ : World) :
  ObsState O → ℕ :=
fun q => if q ∈ PerceptualReappearingStates step O w₀
        then PerceptualValue_count M step O w₀ q
        else 0

/-- Observer rank function: same as blink function for generality -/
def observer_rank_function := observer_blink_function

/-- Recurrent states have positive value if M is large enough -/
theorem recurrent_has_positive_value {M : ℕ} (step : World → World) (O : Observer World) (w₀ : World)
    (q : ObsState O) (hq : q ∈ PerceptualReappearingStates step O w₀)
    (hM : ∃ k < M, obsTrajectory step O w₀ k = q) :
    observer_blink_function M step O w₀ q > 0 :=
by
  simp [observer_blink_function, hq]
  obtain ⟨k, hkM, hkq⟩ := hM
  have hk_range : k ∈ Finset.range M := Finset.mem_range.2 hkM
  have hk_filter : k ∈ (Finset.range M).filter (fun n => obsTrajectory step O w₀ n = q) :=
    Finset.mem_filter.2 ⟨hk_range, hkq⟩
  exact Finset.card_pos.2 ⟨k, hk_filter⟩

-------------------------------------------------------------------------------
-- 3. Observer Oracle: Minimal Detection Step
-------------------------------------------------------------------------------

/-- Minimal number of steps needed to detect a perceptual state `q` -/
noncomputable def M_min (step : World → World) (O : Observer World) (w₀ : World) (q : ObsState O) : ℕ :=
  if h : InfinitelyRecurrent step O w₀ q then
    have _ : DecidablePred (fun n => obsTrajectory step O w₀ n = q) := Classical.decPred _
    Nat.find (infinite.nonempty h) + 1
  else 0

/-- Guarantee: observer detects `q` using M_min -/
theorem observer_oracle_detects (step : World → World) (O : Observer World) (w₀ : World) (q : ObsState O)
    (hq : q ∈ PerceptualReappearingStates step O w₀) :
    observer_blink_function (M_min step O w₀ q) step O w₀ q > 0 :=
by
  simp [M_min, hq, observer_blink_function]
  have _ : DecidablePred (fun n => obsTrajectory step O w₀ n = q) := Classical.decPred _
  let exists_proof := infinite.nonempty hq
  let m := Nat.find exists_proof
  have hm_spec : obsTrajectory step O w₀ m = q := Nat.find_spec exists_proof
  have hm_range : m ∈ Finset.range (m + 1) := Finset.mem_range.mpr (Nat.lt_succ_self m)
  have hm_filter : m ∈ (Finset.range (m + 1)).filter (fun n => obsTrajectory step O w₀ n = q) :=
    Finset.mem_filter.mpr ⟨hm_range, hm_spec⟩
  exact Finset.card_pos.mpr ⟨m, hm_filter⟩

-------------------------------------------------------------------------------
-- 4. Observer Oracle for Ranking: Minimal Step for Positive Rank
-------------------------------------------------------------------------------

/-- Minimal number of steps to guarantee positive rank assignment -/
noncomputable def M_min_rank (step : World → World) (O : Observer World) (w₀ : World)
    (q : ObsState O) : ℕ :=
if h : q ∈ PerceptualReappearingStates step O w₀ then
  have _ : DecidablePred (fun n => obsTrajectory step O w₀ n = q) := Classical.decPred _
  Nat.find (infinite.nonempty h) + 1
else 0

/-- Guarantee: using M_min_rank, observer_rank_function returns positive value -/
theorem observer_rank_oracle_detects (step : World → World) (O : Observer World) (w₀ : World)
    (q : ObsState O) (hq : q ∈ PerceptualReappearingStates step O w₀) :
    observer_rank_function (M_min_rank step O w₀ q) step O w₀ q > 0 :=
by
  simp [observer_rank_function, M_min_rank, hq]
  have _ : DecidablePred (fun n => obsTrajectory step O w₀ n = q) := Classical.decPred _
  let exists_proof := infinite.nonempty hq
  let m := Nat.find exists_proof
  have hm_spec : obsTrajectory step O w₀ m = q := Nat.find_spec exists_proof
  have hm_range : m ∈ Finset.range (m + 1) := Finset.mem_range.mpr (Nat.lt_succ_self m)
  have hm_filter : m ∈ (Finset.range (m + 1)).filter (fun n => obsTrajectory step O w₀ n = q) :=
    Finset.mem_filter.mpr ⟨hm_range, hm_spec⟩
  exact Finset.card_pos.mpr ⟨m, hm_filter⟩

-------------------------------------------------------------------------------
-- 5. Ecological Interpretation
-------------------------------------------------------------------------------

/-!
PerceptualReappearanceOracleFull:

• Observer recognizes and assigns positive value to recurrent perceptual states.
• Minimal detection function M_min guarantees finite detection.
• Minimal rank detection function M_min_rank guarantees positive rank assignment.
• Recurrence knowledge is encoded without agency or control.
• “Here I am again” becomes actionable information.
• Fully composable with harmonizer / attractor ecology framework.
• Provides a complete, constructive, observer-centric perceptual ecology.
-/
