import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.Cast.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Tactic.Linarith

universe u

/-
  =========================
  Core Structures
  =========================
-/

structure Basin where
  name : String
  deriving DecidableEq, BEq

structure Agent where
  name           : String
  exposure_count : ℕ
  memory         : Finset Basin
  utility        : ℝ
  cost           : ℝ

/-
  =========================
  Environment Parameters
  =========================
-/

variable (Basins : Finset Basin)

/-- 
Observed effect of adopting a basin’s asymmetry.
Positive = helps agent’s current goal,
Negative = works against it,
Zero = irrelevant.
-/
variable (observed_impact : Agent → Basin → ℝ)

/--
Cost/friction/risk of adopting the basin’s asymmetry.
Captures learning cost, switching cost, risk, etc.
-/
variable (adoption_cost : Agent → Basin → ℝ)

/-
  =========================
  Exposure Learning Core
  =========================
-/

/--
Adaptive threshold:
Starts conservative and relaxes with both
(1) exposure count and
(2) diversity of remembered basins.
-/
def adaptive_threshold (A : Agent) : ℝ :=
  3.0
    - A.exposure_count.to_real * 0.1
    - A.memory.card.to_real * 0.05

/-- Net surplus from adoption --/
def net_gain (A : Agent) (B : Basin) : ℝ :=
  observed_impact A B - adoption_cost A B

/--
Goal compatibility:
Adopt only if net gain clears current risk threshold.
-/
def should_adopt (A : Agent) (B : Basin) : Prop :=
  net_gain observed_impact adoption_cost A B > adaptive_threshold A

/--
Single observation step.
Always increases exposure.
Adoption happens only when surplus clears threshold.
-/
def observe (A : Agent) (B : Basin) : Agent :=
  let new_exposure := A.exposure_count + 1
  if h : should_adopt observed_impact adoption_cost A B then
    { A with
      exposure_count := new_exposure
      memory         := A.memory.insert B
      utility        := A.utility + observed_impact A B
      cost           := A.cost + adoption_cost A B }
  else
    { A with exposure_count := new_exposure }

/-
  =========================
  Basic Lemmas
  =========================
-/

/-- Exposure strictly increases on every observation --/
theorem exposure_strictly_increases (A : Agent) (B : Basin) :
    (observe observed_impact adoption_cost A B).exposure_count
      = A.exposure_count + 1 := by
  unfold observe
  split <;> simp

/-- If adoption occurs, net value strictly increases --/
theorem adoption_improves_net_value (A : Agent) (B : Basin)
    (h : should_adopt observed_impact adoption_cost A B) :
    (observe observed_impact adoption_cost A B).utility
      - (observe observed_impact adoption_cost A B).cost
    >
    A.utility - A.cost := by
  unfold observe
  simp [h, should_adopt, net_gain] at *
  linarith

/-- If no adoption, net value remains unchanged --/
theorem no_adoption_net_constant (A : Agent) (B : Basin)
    (h : ¬ should_adopt observed_impact adoption_cost A B) :
    (observe observed_impact adoption_cost A B).utility
      - (observe observed_impact adoption_cost A B).cost
    =
    A.utility - A.cost := by
  unfold observe
  simp [h]

/-
  =========================
  Exposure Step Operator
  =========================
-/

/--
One exposure step:
If there exists an adoptable basin, observe one such basin.
Otherwise, agent remains unchanged.
-/
noncomputable def exposure_step (A : Agent) : Agent :=
  if h : ∃ B ∈ Basins, should_adopt observed_impact adoption_cost A B then
    let ⟨B, _, hB⟩ := Classical.choose h
    observe observed_impact adoption_cost A B
  else
    A

/-
  =========================
  Exposure Learning Law
  =========================
-/

/--
Exposure Learning Law:

There exists a trajectory of exposure-driven updates
along which the agent’s net value (utility − cost)
is monotone non-decreasing.

This holds under minimal assumptions:
- bounded rationality
- selective adoption
- explicit costs
- exposure-driven calibration
-/
theorem exposure_learning_law :
  ∀ (A₀ : Agent),
    ∃ f : ℕ → Agent,
      f 0 = A₀ ∧
      ∀ n,
        (f n).utility - (f n).cost
          ≤
        (f (n+1)).utility - (f (n+1)).cost := by
  intro A₀
  use fun n => Nat.iterate exposure_step n A₀
  constructor
  · rfl
  · intro n
    unfold exposure_step
    by_cases h :
      ∃ B ∈ Basins,
        should_adopt observed_impact adoption_cost
          (Nat.iterate exposure_step n A₀) B
    ·
      obtain ⟨B, hB, hAdopt⟩ := h
      have hGain :=
        adoption_improves_net_value
          observed_impact adoption_cost
          (Nat.iterate exposure_step n A₀) B hAdopt
      simp [h, hGain, Classical.choose_spec h]
    ·
      simp [h]

/-
  =========================
  Interpretation Notes
  =========================

  • No notion of “good” or “bad” is absolute.
    Only goal-relative surplus matters.

  • Exposure is not assumed to be beneficial.
    Only selective, surplus-positive adoption is allowed.

  • Poverty traps are not ruled out.
    This theorem only proves adaptive capacity via exposure.

  • Brute-force learning and internal computation
    remain possible but are outside this model.

  • Infrastructure, culture, and institutions act by
    increasing observable basins — exposure rate —
    not by forcing outcomes.

-/
