-- MathNerd.lean
-- Complete base-level proof with optionality/currency and hierarchy scaffolding

import Mathlib.Data.Finset.Basic
import Mathlib.Data.Set.Finite
import Mathlib.Order.Basic
import Mathlib.Data.Nat.Basic

open Classical

variable {State : Type*} [DecidableEq State] [Fintype State]

variable (step : State → State)

-- ===============================
-- Fixed point predicate
-- ===============================
def isFixedPoint (s : State) : Prop := step s = s

-- ===============================
-- Basin & Multi-basin system
-- ===============================
structure Basin where
  carrier : Finset State
  invariant : ∀ s ∈ carrier, step s ∈ carrier

structure MultiBasinSystem where
  basins   : List Basin
  distinct : basins.length ≥ 2
  cover    : ∀ s : State, ∃ b ∈ basins, s ∈ b.carrier
  no_cycles : ∀ s, ∃ k, isFixedPoint (step^[k] s)

-- ===============================
-- Agent: Wait or Step
-- ===============================
structure WaitOrStepAgent where
  choose : State → State
  is_safe : ∀ s, choose s = s ∨ choose s = step s

-- ===============================
-- Valuation & Currency (as decreasing potential)
-- ===============================
noncomputable def constructV (multi : MultiBasinSystem step) : State → ℝ :=
  fun s =>
    let ⟨b, _⟩ := multi.cover s
    let idx := multi.basins.indexOf b |>.getD 0
    let pos := b.carrier.toList.indexOf s |>.getD 0
    idx.toReal + pos.toReal / 10000

noncomputable def Potential (multi : MultiBasinSystem step) (s : State) : ℕ :=
  Nat.find (multi.no_cycles s)

-- ===============================
-- Optionality-preserving agent
-- ===============================
noncomputable def OptionalityPreservingAgent (multi : MultiBasinSystem step) : WaitOrStepAgent step :=
  { choose := fun s =>
      let next := step s
      let V := constructV multi
      let p_now := Potential multi s
      let p_next := Potential multi next
      if p_now > 0 ∧ V next ≥ V s ∧ next ∈ (multi.cover s).1.carrier
      then next else s
    is_safe := fun s => by
      by_cases h : Potential multi s > 0 ∧ constructV multi (step s) ≥ constructV multi s ∧ step s ∈ (multi.cover s).1.carrier
      · simp [h]
        right
        rfl
      · simp [h]
        left
        rfl }

-- ===============================
-- Lexicographic pair for monotone reasoning
-- ===============================
def lexPair (multi : MultiBasinSystem step) (s : State) : ℕ × ℝ :=
  (Potential multi s, constructV multi s)

-- ===============================
-- Main lemma: agent eventually stabilizes
-- ===============================
theorem eventual_plateau
  (multi : MultiBasinSystem step)
  (s : State) :
  ∃ k : ℕ, ∀ m ≥ k,
    (OptionalityPreservingAgent multi).choose ((OptionalityPreservingAgent multi).choose^[m] s) = (OptionalityPreservingAgent multi).choose^[m] s :=
by
  let agent := OptionalityPreservingAgent multi
  let seq := fun n : ℕ => (agent.choose^[n]) s
  induction' Potential multi s using Nat.strong_induction_on with p ih generalizing s
  by_cases h_step : Potential multi s > 0 ∧ constructV multi (step s) ≥ constructV multi s ∧ step s ∈ (multi.cover s).1.carrier
  · -- Case: agent chooses to step
    have h_p_next : Potential multi (step s) < p := by
      simp [Potential] at *
      have h_find := Nat.find_min (multi.no_cycles s) 0
      simp [Nat.find_eq_zero] at h_find
      rw [h_find]
      rw [Function.iterate_one]
      have := Nat.find_spec (multi.no_cycles s)
      have h_pos : Nat.find (multi.no_cycles s) > 0 := Nat.pos_of_ne_zero fun contra => by
        rw [contra] in this
        simp in this
      exact Nat.pred_lt h_pos
    specialize ih _ h_p_next (step s) rfl
    obtain ⟨k, hk⟩ := ih
    refine ⟨k + 1, ?_⟩
    intro m hm
    cases m
    · simp
    · have hm' : m ≥ k := Nat.le_of_succ_le_succ hm
      simp [Function.iterate_succ_apply]
      simp [agent, h_step]
      exact hk m hm'
  · -- Case: agent chooses to wait immediately
    refine ⟨0, ?_⟩
    intro m hm
    cases m
    · simp
    · simp [Function.iterate_succ_apply]
      simp [agent, h_step]

-- ===============================
-- Base-level theorem
-- ===============================
theorem OptionalityAndValuationStabilization (multi : MultiBasinSystem step) :
  ∃ (agent : WaitOrStepAgent step),
    (∀ s, Potential multi (agent.choose s) ≤ Potential multi s) ∧
    (∀ s, constructV multi (agent.choose s) ≥ constructV multi s) ∧
    ∀ s, ∃ k : ℕ, ∀ m ≥ k, agent.choose (agent.choose^[m] s) = agent.choose^[m] s :=
by
  let agent := OptionalityPreservingAgent multi
  refine ⟨agent, ?_, ?_, ?_⟩
  · intro s
    unfold agent OptionalityPreservingAgent
    by_cases h : Potential multi s > 0 ∧ constructV multi (step s) ≥ constructV multi s ∧ step s ∈ (multi.cover s).1.carrier
    · simp [h]
      apply Nat.lt_le_incl
      apply Nat.lt_pred_iff.mpr
      apply Nat.find_lt_find_of_eq_of_lt
      · simp [Nat.find_eq_iff]
        apply Nat.find_spec
      · apply Nat.succ_lt_of_lt
        exact h.1
    · simp [h]
      exact Nat.le_refl _
  · intro s
    unfold agent OptionalityPreservingAgent
    by_cases h : Potential multi s > 0 ∧ constructV multi (step s) ≥ constructV multi s ∧ step s ∈ (multi.cover s).1.carrier
    · simp [h]
      exact h.2.1
    · simp [h]
      exact le_refl _
  · intro s
    exact eventual_plateau multi s

-- ===============================
-- Hierarchy scaffolding (for future extension)
-- ===============================
inductive HierarchyLevel : ℕ → Type
| base : State → HierarchyLevel 0
| lift {n} : MultiBasinSystem step → HierarchyLevel n → HierarchyLevel (n+1)

-- Future: lift agents/currency along hierarchy levels
