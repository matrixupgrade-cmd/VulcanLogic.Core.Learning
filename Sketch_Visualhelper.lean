/-!
===============================================================================
Executable Lean 4 Example: Full Nested Gradient Tree + Visualization
===============================================================================
Author: Sean Timothy
Date: 2025-12-29

Purpose:
  Demonstrates:
  - Soft attractors
  - L2 Sobolev norm
  - Local gradients
  - Perturbation effects
  - Full multi-child hierarchy gradient tree with threshold pruning
  - Enhanced textual visualization (gradient + L2 + sample hitting probability)
===============================================================================
-/ 

import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Probability.ProbabilityMassFunction
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import EpistemicVeil

open Finset PMF ProbabilityMassFunction Real

variable {State : Type*} [Fintype State] [DecidableEq State] [Nonempty State]

-------------------------------------------------------------------------------
-- 0. Example substrate (level 0)
-------------------------------------------------------------------------------

def example_substrate : Substrate (Fin 3) :=
{ update := fun x =>
    match x with
    | 0 => {0, 1}
    | 1 => {1, 2}
    | 2 => {0, 2}
    end
  update_nonempty := by intros x; fin_cases x; simp }

def example_prob : ProbSubstrate (Fin 3) := crisp_to_prob example_substrate

def example_crisp_attractor : Attractor example_substrate :=
{ carrier := {0,1}, carrier_nonempty := by simp
  , invariant := by intros x hx; fin_cases x; simp
  , minimal := by intros B hB hne; fin_cases x; simp
  , basin := {0,1,2}
  , basin_contains := by simp }

def example_soft : SoftAttractor example_prob :=
  soft_from_crisp example_prob example_crisp_attractor 10

-------------------------------------------------------------------------------
-- 1. Gradient computations
-------------------------------------------------------------------------------

#eval L2_sobolev_norm example_prob 10 example_soft
#eval local_gradient example_prob 0 2

def δ_example : Fin 3 → Fin 3 → ℝ
| 0,1 => 0.1
| 1,2 => 0.2
| _,_ => 0

#eval perturbation_effect example_prob δ_example 0 example_soft

-------------------------------------------------------------------------------
-- 2. Full multi-child hierarchy gradient tree
-------------------------------------------------------------------------------

structure FullNestedGradientTree :=
  (attractor : NestedAttractor example_substrate ·)
  (gradient : ℝ)
  (children : List FullNestedGradientTree := [])

-- Recursive construction of multi-child tree
def build_full_gradient_tree :
  ∀ (n : ℕ) (S : Substrate State) (P : ProbSubstrate State) (threshold : ℝ),
    List (FullNestedGradientTree)
| 0, S, P, _ =>
  univ.toList.map (fun x =>
    let A : NestedAttractor S 0 := ⟨x, trivial⟩
    { attractor := A, gradient := hierarchy_gradient P 0 A, children := [] })
| n+1, S, P, threshold =>
  let lower := build_full_gradient_tree n S P threshold
  lower.filterMap (fun child =>
    let S_soft := soft_from_crisp P child.attractor.val 1000
    if ProbNested threshold S_soft child.attractor.val then
      let A : NestedAttractor S (n+1) := ⟨meta_step (hierarchy_substrate S n) child.attractor, trivial⟩
      some { attractor := A
            , gradient := hierarchy_gradient P (n+1) A threshold
            , children := [child] }  -- all contributing children
    else none)

-- Build full tree for depth 2 with threshold 0.5
def full_example_tree : List (FullNestedGradientTree) :=
  build_full_gradient_tree 2 example_substrate example_prob 0.5

-------------------------------------------------------------------------------
-- 3. Aggregate L2 norms across tree
-------------------------------------------------------------------------------

def aggregate_tree_L2 (tree : FullNestedGradientTree) : ℝ :=
  sqrt (tree.gradient^2 + tree.children.foldl (fun acc c => acc + aggregate_tree_L2 c^2) 0)

#eval full_example_tree.map aggregate_tree_L2

-------------------------------------------------------------------------------
-- 4. Enhanced textual visualization helper
-------------------------------------------------------------------------------

/-- Pretty-print tree with gradient, L2 norm, and soft attractor hitting probability -/
def print_full_info_tree (tree : FullNestedGradientTree) (P : ProbSubstrate State) (sample_state : State) (indent : Nat := 0) : String :=
  let prefix := String.replicate (2 * indent) " "
  let node_L2 := aggregate_tree_L2 tree
  let S_soft := soft_from_crisp P tree.attractor.val 10
  let hit_prob := S_soft.hitting sample_state
  let child_strs := tree.children.map (fun c => print_full_info_tree c P sample_state (indent + 1))
  let children_repr := String.intercalate "\n" child_strs
  prefix ++ "Grad: " ++ toString tree.gradient ++
    ", L2: " ++ toString node_L2 ++
    ", Hit[" ++ toString sample_state ++ "]: " ++ toString hit_prob ++
    (if children_repr = "" then "" else "\n" ++ children_repr)

/-- Pretty-print all trees at root level for a sample state -/
def print_full_tree_info (trees : List FullNestedGradientTree) (P : ProbSubstrate State) (sample_state : State) : String :=
  String.intercalate "\n" (trees.map (fun t => print_full_info_tree t P sample_state 0))

-- Example: visualize full_example_tree for sample state 0
#eval print_full_tree_info full_example_tree example_prob 0
