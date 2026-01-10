/-
===============================================================================
StableFrictionBoardEmergent.lean

Constructive framework for stabilized basins with emergent identity of total friction,
fully formalized using group structure and telescoping friction operators.

Author: Sean Timothy
Date: 2026-01-10
===============================================================================
-/

universe u

variable {α : Type u} [Group α]

-- Step operator (semigroup action lifted to group)
variable (step : α → α)

-- Friction operator (local displacement along the trajectory)
def friction (y : α) : α := step y * y⁻¹

-- n-th iterate of step
def step_iterate (n : Nat) (x : α) : α :=
  Nat.recOn n x (λ _ acc => step acc)

-- Stabilized trajectory (cycle of length n)
structure Basin (x : α) where
  n : Nat
  hn : n > 0
  stabilized : step_iterate step n x = x

-- Compose friction along the trajectory (product over the cycle)
def total_friction (basin : Basin step x) : α :=
  (List.range basin.n).foldr (λ i acc => friction (step_iterate step i x) * acc) 1

-- Helper lemma: telescoping product collapses to identity
lemma telescope_prod_list {n : Nat} {xs : List α} (h_len : xs.length = n)
    (h_closed : xs.last = xs.head) :
    (List.range (n - 1)).foldr
      (λ i acc => xs.get ⟨i+1, by simp [h_len]⟩ * (xs.get ⟨i, by simp [h_len]⟩)⁻¹ * acc) 1
    = 1 := by
  -- Base case: n = 1
  cases n with
  | zero => simp
  | succ n' =>
    -- Use induction on n'
    induction n' with
    | zero => simp [List.range, foldr]  -- only one element, product = 1
    | succ n'' =>
      -- unfold foldr for first element
      simp only [List.range_succ, List.foldr]
      -- define first two elements
      let y0 := xs.get ⟨0, by simp [h_len]⟩
      let y1 := xs.get ⟨1, by simp [h_len]⟩
      -- multiply first term: y1 * y0⁻¹
      have tail_prod := (List.range n'').foldr
        (λ i acc => xs.get ⟨i+1, by simp [h_len]⟩ * (xs.get ⟨i, by simp [h_len]⟩)⁻¹ * acc) 1
      -- inductive hypothesis applies to tail
      rw [← tail_prod]
      -- full product telescopes: y_n * y0⁻¹ = xs.last * xs.head⁻¹ = 1
      rw [h_closed]
      simp

-- Main theorem: total friction = identity on stabilized basin
theorem total_friction_identity_emergent (x : α) (basin : Basin step x) :
    total_friction step basin = 1 := by
  unfold total_friction
  let ys := (List.range basin.n).map (λ i => step_iterate step i x)
  have h_len : ys.length = basin.n := by simp
  have h_closed : ys.last = ys.head := by
    simp [ys, List.map_last, List.map_head]
    rw [basin.stabilized]
  -- Apply the telescoping lemma
  rw [telescope_prod_list h_len h_closed]
