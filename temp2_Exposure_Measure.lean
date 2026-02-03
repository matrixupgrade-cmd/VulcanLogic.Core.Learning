import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Data.Nat.Cast.Basic
import Mathlib.Data.Finset.Basic

universe u

-- Basin Structure: Define Basin and make it comparable
structure Basin where
  name : String
  deriving DecidableEq, BEq

-- Agent Structure: Track goal utility, memory, and exposure
structure Agent where
  name           : String
  goal_utility   : ℝ
  exposure_count : ℕ
  memory         : Finset Basin   -- no duplicates, easy cardinality

variable (Basins : List Basin)

-- Parameter: how adopting B's asymmetry affects agent's goal performance
-- (positive = helpful in current goal frame, negative = harmful, zero = irrelevant)
variable (observed_impact : Agent → Basin → ℝ)

-- Adaptive threshold: relaxing with exposure, but also based on diversity in memory
def adaptive_threshold (A : Agent) : ℝ :=
  3.0 - (A.exposure_count.to_real * 0.1) - (A.memory.card.to_real * 0.05)

-- Goal Compatibility: Is B's asymmetry compatible with Agent's goal?
def goal_compatible (A : Agent) (B : Basin) : Prop :=
  observed_impact A B > adaptive_threshold A

-- Non-goal Compatible Feedback: Track basins with negative impacts
def negative_feedback (A : Agent) (B : Basin) : Prop :=
  observed_impact A B ≤ adaptive_threshold A

-- Should Adopt: Basin is compatible with current goal
def should_adopt (A : Agent) (B : Basin) : Prop :=
  goal_compatible A B

-- Core observation step: always +1 exposure, adopt if compatible, penalize negatives
def observe (A : Agent) (B : Basin) : Agent :=
  let new_count := A.exposure_count + 1
  let delta := observed_impact A B
  let new_utility := A.goal_utility + delta
  if should_adopt A B then
    { A with
      exposure_count := new_count,
      memory         := A.memory.insert B,
      goal_utility   := new_utility }
  else if negative_feedback A B then
    { A with
      exposure_count := new_count,
      goal_utility   := new_utility - 0.02 }   -- small, tunable penalty for bad signals
  else
    { A with exposure_count := new_count }

/-- Thm 1: Exposure + diversity always relaxes threshold --/
theorem threshold_relaxes_on_exposure_or_diversity (A : Agent) :
    adaptive_threshold { A with exposure_count := A.exposure_count + 1 } <
    adaptive_threshold A := by
  unfold adaptive_threshold
  simp only [Nat.to_real_add_one]
  linarith

theorem threshold_relaxes_on_memory_growth (A : Agent) (B : Basin) (h_new : B ∉ A.memory) :
    adaptive_threshold { A with memory := A.memory.insert B } <
    adaptive_threshold A := by
  unfold adaptive_threshold
  simp only [Finset.card_insert_of_not_mem h_new]
  linarith

-- Thm 2: Adoption strictly increases utility
theorem adoption_increases_utility (A : Agent) (B : Basin)
    (h : should_adopt A B) :
    (observe A B).goal_utility > A.goal_utility := by
  unfold observe
  simp only [h, if_pos h]
  exact h

-- Thm 3: Exposure always increases by 1
theorem exposure_strictly_increases (A : Agent) (B : Basin) :
    (observe A B).exposure_count = A.exposure_count + 1 := rfl

-- Goal shift (re-framing success)
def shift_goal (A : Agent) (new_impact : Agent → Basin → ℝ) : Agent :=
  { A with goal_utility := new_impact A A }  -- re-evaluate self under new lens

-- Optional: small bonus for confirming existing good patterns
def is_symmetry (A : Agent) (B : Basin) : Prop :=
  observed_impact A B ≥ 0 ∧ B ∈ A.memory

def reinforce_symmetry (A : Agent) (B : Basin) (h : is_symmetry A B) : Agent :=
  { A with goal_utility := A.goal_utility + 0.03 }  -- small confidence boost
