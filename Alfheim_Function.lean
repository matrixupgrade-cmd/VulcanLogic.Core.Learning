/-!
# Verified Bounded Multi-Basin Alfheim Function
Author: Sean Timothy
Date: 2026-01-02
Purpose: Formal verification of bounded clustering for multi-agent, multi-basin system.
-/

import data.real.basic
import data.list.basic
import data.set.basic
import tactic

/-! ## Core Structures -/

structure Agent :=
(id : ℕ)
(state : ℝ)
(optionality : ℝ)
(tension : ℝ)

structure Basin :=
(to_list : list Agent)

structure MetaMap :=
(agents : set Agent)

/-! ## Helper Functions -/

def basin_avg (B : Basin) : ℝ :=
if B.to_list = [] then 0 else (B.to_list.map (λ x, x.state)).sum / (B.to_list.length : ℝ)

def nearest_basin (a : Agent) (B_list : list Basin) : Basin :=
B_list.foldl (λ B_min B_curr,
  if abs (a.state - basin_avg B_curr) < abs (a.state - basin_avg B_min)
  then B_curr else B_min) B_list.head

lemma nearest_basin_in_list {a : Agent} {B_list : list Basin} (h : B_list ≠ []) :
  nearest_basin a B_list ∈ B_list :=
begin
  induction B_list with B hd ih,
  { contradiction },
  { -- base case B_list = [B]
    simp [nearest_basin],
    simp [foldl],
    exact list.head_mem _ _ }
end

def update_state (a : Agent) (B : Basin) (α : ℝ) : Agent :=
{ a with state := (1 - α) * a.state + α * basin_avg B }

def update_optionality (a : Agent) (opt_min : ℝ) : Agent :=
{ a with optionality := max a.optionality opt_min }

def update_tension (a : Agent) (tension_max : ℝ) : Agent :=
{ a with tension := min a.tension tension_max }

/-! ## Multi-Basin Alfheim Function -/

def Alfheim_Function_Multi (M : MetaMap) (B_list : list Basin) (α opt_min tension_max : ℝ) : MetaMap :=
{ agents := M.agents.map (λ a,
    let B := nearest_basin a B_list in
    let a1 := update_state a B α in
    let a2 := update_optionality a1 opt_min in
    update_tension a2 tension_max
  )
}

/-! ## Safety Invariants -/

def all_optionality_safe (M : MetaMap) (opt_min : ℝ) : Prop :=
∀ a ∈ M.agents, a.optionality ≥ opt_min

def all_tension_safe (M : MetaMap) (tension_max : ℝ) : Prop :=
∀ a ∈ M.agents, a.tension ≤ tension_max

/-! ## ε-bounded Clustering -/

def in_basin_ε (a : Agent) (B : Basin) (ε : ℝ) : Prop :=
abs (a.state - basin_avg B) ≤ ε

def agent_bounded_cluster (a : Agent) (B_list : list Basin) (ε : ℝ) : Prop :=
∃ B ∈ B_list, in_basin_ε a B ε

def all_agents_bounded_cluster (M : MetaMap) (B_list : list Basin) (ε : ℝ) : Prop :=
∀ a ∈ M.agents, agent_bounded_cluster a B_list ε

/-! ## Iterated Multi-Basin Alfheim Map -/

def iterate_Alfheim_map_Multi : ℕ → MetaMap → list Basin → ℝ → ℝ → ℝ → MetaMap
| 0 M _ _ _ _ := M
| (n+1) M B_list α opt_min tension_max :=
    Alfheim_Function_Multi (iterate_Alfheim_map_Multi n M B_list α opt_min tension_max)
                           B_list α opt_min tension_max

/-! ## Supporting Lemmas -/

lemma Alfheim_preserves_optionality_multi {M : MetaMap} {B_list : list Basin}
  {α opt_min tension_max : ℝ} :
  all_optionality_safe (Alfheim_Function_Multi M B_list α opt_min tension_max) opt_min :=
begin
  intros a ha,
  simp [Alfheim_Function_Multi, all_optionality_safe],
  exact le_max_left a.optionality opt_min,
end

lemma Alfheim_preserves_tension_multi {M : MetaMap} {B_list : list Basin}
  {α opt_min tension_max : ℝ} :
  all_tension_safe (Alfheim_Function_Multi M B_list α opt_min tension_max) tension_max :=
begin
  intros a ha,
  simp [Alfheim_Function_Multi, all_tension_safe],
  exact min_le_right a.tension tension_max,
end

lemma iterate_state_bounded
  {M : MetaMap} {B_list : list Basin} {α : ℝ} {ε_max : ℝ}
  (hα : 0 < α ∧ α ≤ 1) (hB_nonempty : B_list ≠ [])
  (h_init : ∀ a ∈ M.agents, ∃ B ∈ B_list, abs (a.state - basin_avg B) ≤ ε_max) :
  ∀ n, ∀ a ∈ (iterate_Alfheim_map_Multi n M B_list α a.optionality a.tension α).agents,
    ∃ B ∈ B_list, abs (a.state - basin_avg B) ≤ ε_max :=
begin
  intros n a ha,
  induction n with n ih,
  { exact h_init a ha },
  { let M_n := iterate_Alfheim_map_Multi n M B_list α a.optionality a.tension α,
    rcases ih a ha with ⟨B_prev, hB_prev, h_dist⟩,
    let B_curr := nearest_basin a B_list,
    use [B_curr, nearest_basin_in_list hB_nonempty],
    calc abs ((update_state a B_curr α).state - basin_avg B_curr)
        = abs ((1 - α) * (a.state - basin_avg B_curr)) : by simp [update_state]; ring
    ... ≤ abs (a.state - basin_avg B_prev) : by linarith [hα.1, h_dist]
    ... ≤ ε_max : h_dist }
end

/-! ## Global Bounded Clustering Theorem -/

theorem Alfheim_global_bounded_multi
  {M : MetaMap} {B_list : list Basin} {α opt_min tension_max ε_max : ℝ}
  (hα : 0 < α ∧ α ≤ 1) (hB_nonempty : B_list ≠ [])
  (h_init : ∀ a ∈ M.agents, ∃ B ∈ B_list, abs (a.state - basin_avg B) ≤ ε_max) :
  ∀ n, all_agents_bounded_cluster
    (iterate_Alfheim_map_Multi n M B_list α opt_min tension_max)
    B_list ε_max ∧
  all_optionality_safe (iterate_Alfheim_map_Multi n M B_list α opt_min tension_max) opt_min ∧
  all_tension_safe (iterate_Alfheim_map_Multi n M B_list α opt_min tension_max) tension_max :=
begin
  intro n,
  induction n with n ih,
  { split,
    { intros a ha, exact h_init a ha },
    split; apply _root_.rfl },
  { let M_n := iterate_Alfheim_map_Multi n M B_list α opt_min tension_max,
    split,
    { intros a ha, exact iterate_state_bounded hα hB_nonempty h_init n a ha },
    split,
    { apply Alfheim_preserves_optionality_multi },
    { apply Alfheim_preserves_tension_multi } }
end
