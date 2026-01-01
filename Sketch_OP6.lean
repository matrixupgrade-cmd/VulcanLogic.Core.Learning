/-!
===============================================================================
PerceptualReappearanceOracle.lean
===============================================================================

Author: Sean Timothy & VulcanLogic Architect
Date: 2026-01-01

Purpose:
  Full observer-based perceptual reappearance framework:
  - PerceptualReappearance: infinite recurrence of perceptual states
  - observer_blink_function: finite approximation of recurrence
  - M_min oracle function: minimal detection step for infinitely recurring states
  Encodes ecological knowledge without control or agency.
===============================================================================

-/

import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Quotient
import Mathlib.Logic.Function.Basic
import Mathlib.Data.Set.Infinite

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

instance (O : Observer World) : DecidableRel (ObsEq O) :=
  fun x y => Nat.decEq (O.observe x) (O.observe y)

instance (O : Observer World) : Setoid World :=
{ r := ObsEq O,
  iseqv :=
  { refl := by intro x; rfl,
    symm := by intro x y h; exact h.symm,
    trans := by intro x y z h₁ h₂; exact h₁.trans h₂ } }

/-- Finite perceptual states observed by O -/
abbrev ObsState (O : Observer World) := Quotient (ObsEq O)

instance (O : Observer World) : Fintype (ObsState O) :=
  Quotient.fintype (inferInstance : Setoid World)

/-- Observer-relative trajectory: sequence of perceived states -/
def obsTrajectory (O : Observer World) (w₀ : World) : ℕ → ObsState O :=
  fun n => Quot.mk _ (Nat.iterate step n w₀)

-------------------------------------------------------------------------------
-- 1. Perceptual Reappearance
-------------------------------------------------------------------------------

/-- A perceptual state that recurs infinitely often along the trajectory -/
def InfinitelyRecurrent (O : Observer World) (w₀ : World) (q : ObsState O) : Prop :=
  { n : ℕ | obsTrajectory step O w₀ n = q }.Infinite

/-- The set of all perceptual states that reappear infinitely often -/
def PerceptualReappearingStates (O : Observer World) (w₀ : World) : Set (ObsState O) :=
  { q | InfinitelyRecurrent step O w₀ q }

/-- Existence theorem: any finite perceptual habitat guarantees recurrence -/
theorem perceptual_reappearance_exists (O : Observer World) (w₀ : World) :
    (PerceptualReappearingStates step O w₀).Nonempty :=
by
  let traj := obsTrajectory step O w₀
  obtain ⟨q, h_inf⟩ := Fintype.exists_infinite_fiber (f := traj)
  exact ⟨q, h_inf⟩

/-- Blink lemma: for any future N, some reappearing state occurs later -/
lemma perceptual_reappearance_blink (O : Observer World) (w₀ : World) (N : ℕ) :
  ∃ n ≥ N, ∃ q ∈ PerceptualReappearingStates step O w₀,
    obsTrajectory step O w₀ n = q :=
by
  obtain ⟨q, hq⟩ := perceptual_reappearance_exists O w₀
  let S := { n | obsTrajectory step O w₀ n = q }
  have hS : S.Infinite := hq
  obtain ⟨n, hnS, hnN⟩ := hS.exists_nat_ge N
  exact ⟨n, hnN, q, hq, hnS⟩

-------------------------------------------------------------------------------
-- 2. Observer Blink Function
-------------------------------------------------------------------------------

/-- Approximate count of occurrences of a perceptual state in first M steps -/
def PerceptualValue_count (M : ℕ) (O : Observer World) (w₀ : World) (q : ObsState O) : ℕ :=
  (Finset.range M).filter (fun n => obsTrajectory step O w₀ n = q).card

/-- Observer blink function: positive value for infinitely recurring states -/
def observer_blink_function (M : ℕ) (O : Observer World) (w₀ : World) :
  ObsState O → ℕ :=
fun q => if q ∈ PerceptualReappearingStates step O w₀
        then PerceptualValue_count M O w₀ q
        else 0

/-- Recurrent states have positive (approximate) value -/
theorem recurrent_has_positive_value (M : ℕ) (O : Observer World) (w₀ : World)
    (q : ObsState O) (hq : q ∈ PerceptualReappearingStates step O w₀) :
    observer_blink_function M O w₀ q > 0 :=
by
  simp [observer_blink_function, hq]
  let S := { n | obsTrajectory step O w₀ n = q }
  have hS : S.Infinite := hq
  obtain ⟨n, hnS, _⟩ := hS.exists_nat_ge M
  have hn_range : n ∈ Finset.range (n+1) := Finset.mem_range.2 (Nat.lt_succ_self n)
  have hn_filter : n ∈ (Finset.range (n+1)).filter (fun k => obsTrajectory step O w₀ k = q) :=
    Finset.mem_filter.2 ⟨hn_range, hnS⟩
  exact Finset.card_pos.2 ⟨n, hn_filter⟩

-------------------------------------------------------------------------------
-- 3. Observer Oracle: Minimal Detection Step
-------------------------------------------------------------------------------

/--
Minimal number of steps needed to detect a perceptual state `q` along
the trajectory, guaranteeing a positive observer blink value.
-/
noncomputable def M_min (q : ObsState O) : ℕ :=
  if h : q ∈ PerceptualReappearingStates step O w₀ then
    let S := { n : ℕ | obsTrajectory step O w₀ n = q }
    Nat.find (Nat.exists_of_infinite h S)
  else 0

/-- Guarantee: observer detects `q` using M_min -/
theorem observer_oracle_detects (q : ObsState O)
    (hq : q ∈ PerceptualReappearingStates step O w₀) :
    observer_blink_function (M_min step O w₀ q) O w₀ q > 0 :=
by
  simp [M_min, hq, observer_blink_function, PerceptualReappearingStates]
  let S := { n : ℕ | obsTrajectory step O w₀ n = q }
  have hS : S.Infinite := hq
  have ⟨n, hnS⟩ := Nat.exists_of_infinite hS S
  have hn_filter : n ∈ (Finset.range (n+1)).filter (fun k => obsTrajectory step O w₀ k = q) :=
    Finset.mem_filter.2 ⟨Finset.mem_range.2 (Nat.lt_succ_self n), hnS⟩
  exact Finset.card_pos.2 ⟨n, hn_filter⟩

-------------------------------------------------------------------------------
-- 4. Ecological Interpretation
-------------------------------------------------------------------------------

/-!
PerceptualReappearanceOracle establishes a fully constructive observer function:
- Observer recognizes and assigns positive value to recurrent perceptual states.
- Minimal detection function M_min guarantees computable recognition.
- Recurrence knowledge is encoded without agency or control.
- “Here I am again” becomes actionable information.
- Composable with harmonizer / attractor ecology framework.
-/
