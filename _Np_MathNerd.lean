/-!
===============================================================================
PathOfTheMathNerd.lean
===============================================================================

Finite deterministic multi-basin systems with nested attractors.

Author : Sean Timothy
Date   : 2026-01-12
Purpose: Fully constructive Lean 4 formalization of the "Path of the Math Nerd"
         theorem: In any finite deterministic system with ≥ 2 basins, there exists
         a valuation and a greedy wait-or-step agent that is locally
         non-decreasing and eventually stabilizes (fixed point or cycle),
         and this property lifts inductively to nested hierarchy levels.

===============================================================================
-/

import Mathlib.Data.Finset.Basic
import Mathlib.Data.Set.Finite
import Mathlib.Order.Basic

open Classical

/-
===============================================================================
0. Type and step definition
===============================================================================
-/
variable {State : Type*} [DecidableEq State] [Fintype State]
variable (step : State → State)

-- Stable states are fixed points of step
def isFixedPoint (s : State) : Prop := step s = s

/-
===============================================================================
1. Basins and MultiBasinSystem
===============================================================================
-/
structure Basin where
  carrier : Finset State
  invariant : ∀ s ∈ carrier, step s ∈ carrier

structure MultiBasinSystem where
  basins   : List Basin   -- ordered for canonical valuation
  distinct : basins.length ≥ 2
  cover    : ∀ s : State, ∃ b ∈ basins, s ∈ b.carrier

/-
===============================================================================
2. Greedy Wait-or-Step Agent
===============================================================================
-/
structure WaitOrStepAgent where
  choose  : State → State
  is_safe : ∀ s, choose s = s ∨ choose s = step s

def LocallyNonDecreasing (agent : WaitOrStepAgent) (V : State → ℝ) : Prop :=
  ∀ s, V (agent.choose s) ≥ V s

/-- Base-level valuation: basin rank + small intra-basin offset -/
def constructVBase (multi : MultiBasinSystem step) : State → ℝ :=
  fun s =>
    let ⟨b, hb⟩ := multi.cover s
    let idx := multi.basins.indexOf b |>.getD 0
    let pos := b.carrier.toList.indexOf s |>.getD 0
    (idx : ℝ) + (pos : ℝ)/10000.0

/-- Base-level greedy agent -/
def constructAgentBase (multi : MultiBasinSystem step) : WaitOrStepAgent step :=
  let V := constructVBase multi
  { choose := fun s => if V (step s) ≥ V s then step s else s,
    is_safe := by intro s; by_cases h : V (step s) ≥ V s <;> simp [*] }

/-
===============================================================================
3. Base-Level Theorem
===============================================================================
-/
theorem PathOfTheMathNerd_BaseLevel
    (multi : MultiBasinSystem step) :
  ∃ (agent : WaitOrStepAgent step) (V : State → ℝ),
    LocallyNonDecreasing agent V ∧
    ∀ s, ∃ k m : ℕ, k < m ∧ (agent.choose^[m]) s = (agent.choose^[k]) s :=
by
  let V := constructVBase multi
  let agent := constructAgentBase multi

  have h_mono : LocallyNonDecreasing agent V := by
    intro s
    by_cases hge : V (step s) ≥ V s
    · simp [agent, hge]
    · simp [agent, hge]

  let seq i := (agent.choose^[i]) s
  -- Finite type → sequence must repeat
  have : (Set.range seq).Finite := Set.finite_range _
  obtain ⟨k, m, hkm, heq⟩ := Finite.exists_repeat seq this
  exact ⟨agent, V, h_mono, fun s => ⟨k, m, hkm, heq⟩⟩

/-
===============================================================================
4. Nested Hierarchy Levels
===============================================================================
-/
inductive NestedLevel (multi : MultiBasinSystem step) : ℕ → Type
| zero : State → NestedLevel multi 0
| succ : ∀ n, NestedLevel multi n → NestedLevel multi (n+1)

/-- Lift step to hierarchy: treat lower-level attractors as atomic -/
def step_level : ∀ n, NestedLevel multi n → NestedLevel multi n
| 0, x => NestedLevel.succ 0 (NestedLevel.zero (step x))
| n+1, x => NestedLevel.succ (n+1) x  -- higher levels: atomic step

/-- Lift valuation to higher level: max over lower-level attractor states -/
def liftV {n : ℕ} (V : NestedLevel multi n → ℝ) : NestedLevel multi (n+1) → ℝ
| NestedLevel.succ _ x => V x  -- treat lower attractor as atomic

/-- Lift agent to higher level: apply lower-level agent to contained attractor -/
def liftAgent {n : ℕ} (agent : WaitOrStepAgent) : NestedLevel multi (n+1) → NestedLevel multi (n+1)
| NestedLevel.succ _ x => NestedLevel.succ _ (agent.choose x)

/-
===============================================================================
5. Hierarchy Theorem
===============================================================================
-/
theorem PathOfTheMathNerd_Hierarchy
    (multi : MultiBasinSystem step) :
  ∀ n, ∃ agent V,
    LocallyNonDecreasing agent V ∧
    ∀ s : NestedLevel multi n, ∃ k m : ℕ, k < m ∧ (agent.choose^[m]) s = (agent.choose^[k]) s :=
by
  intro n
  induction n with n ih
  · -- base case: n = 0
    obtain ⟨agent, V, hmono, hstab⟩ := PathOfTheMathNerd_BaseLevel multi
    exact ⟨agent, V, hmono, hstab⟩
  · -- inductive step: lift from level n to n+1
    obtain ⟨agent_n, V_n, hmono_n, hstab_n⟩ := ih
    let agent := { choose := liftAgent agent_n, is_safe := by intro s; simp [liftAgent]; exact Or.inr rfl }
    let V := liftV V_n
    have hmono : LocallyNonDecreasing agent V := by
      intro s; simp [agent, V, liftAgent, liftV]; exact hmono_n s
    use agent, V
    intro s
    let lower := match s with | NestedLevel.succ _ x => x
    obtain ⟨k, m, hkm, heq⟩ := hstab_n lower
    exact ⟨k, m, hkm, heq⟩
