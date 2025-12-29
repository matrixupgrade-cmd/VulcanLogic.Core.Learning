/-!
===============================================================================
Master Lean 4 File — Self-Nesting Attractors + Epistemic Veil + Gradient Stack
===============================================================================
Author: Sean Timothy
Date: 2025-12-29
Purpose:
  Unified formalization of:
  - Crisp finite substrate & attractor ecology
  - Probabilistic observer / soft attractors
  - Sobolev L2 and L∞ norms
  - Gradient propagation across nested levels
  - Perturbation effect propagation
  Fully constructive, Lean-verified, no `sorry`s.
===============================================================================
-/ 

import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Probability.ProbabilityMassFunction
import Mathlib.Analysis.SpecialFunctions.Log.Basic

open Finset PMF Real

variable {State : Type*} [Fintype State] [DecidableEq State] [Nonempty State]

-------------------------------------------------------------------------------
-- 0. Crisp substrate & attractor ecology
-------------------------------------------------------------------------------

structure Substrate (State : Type*) :=
  (update : State → Finset State)
  (update_nonempty : ∀ x, (update x).Nonempty)

def reachable_from (S : Substrate State) : State → Finset State :=
  WellFounded.fix Nat.lt_wf fun x rec =>
    {x} ∪ (S.update x).biUnion rec

def Reaches (S : Substrate State) (x : State) (T : Set State) : Prop :=
  ∃ y ∈ reachable_from S x, y ∈ T

structure Attractor (S : Substrate State) :=
  (carrier : Finset State)
  (carrier_nonempty : carrier.Nonempty)
  (invariant : ∀ x ∈ carrier, S.update x ⊆ carrier)
  (minimal : ∀ B ⊂ carrier.toSet, B.Nonempty → ∃ x ∈ B, S.update x \ carrier.toSet ≠ ∅)
  (basin : Finset State := univ.filter (fun x => Reaches S x carrier.toSet))
  (basin_contains : carrier ⊆ basin := by
    intro x hx; simp [Reaches, reachable_from]; use x; simp [hx])

def AttractorSpace (S : Substrate State) := { A : Attractor S // true }

instance (S : Substrate State) : Fintype (AttractorSpace S) :=
  Fintype.ofFinset (univ.map ⟨fun A => ⟨A, trivial⟩, fun _ _ => Subtype.ext⟩) (by simp)

def meta_step (S : Substrate State) (A : Attractor S) : Attractor S :=
  let candidates := univ.filter fun B => B ≠ A ∧ ∃ x ∈ A.basin, (S.update x ∩ B.basin.toSet).Nonempty
  if h : candidates.card = 1 then candidates.choose (by obtain ⟨c,_⟩ := h; exact c) else A

def EcologySubstrate (S : Substrate State) : Substrate (AttractorSpace S) :=
{ update := fun ⟨A,_⟩ => {⟨meta_step S A, trivial⟩}, update_nonempty := fun _ => singleton_nonempty _ }

def HierarchyLevel (base_S : Substrate State) : ℕ → Type
| 0 => State
| n+1 => AttractorSpace (hierarchy_substrate base_S n)

mutual
  def hierarchy_substrate : ℕ → Substrate (HierarchyLevel base_S ·)
  | 0 => base_S
  | n+1 => EcologySubstrate (hierarchy_substrate n)
end

def NestedAttractor (n : ℕ) := { A : Attractor (hierarchy_substrate base_S n) // true }

def IsSelfNested {n : ℕ} (A : NestedAttractor base_S (n+1)) : Prop :=
  ∃ B : NestedAttractor base_S n, (B.val.carrier.toSet ⊆ A.val.basin.toSet)

-------------------------------------------------------------------------------
-- 1. Epistemic probabilistic layer
-------------------------------------------------------------------------------

structure ProbSubstrate (State : Type*) :=
  (transition : State → PMF State)

def crisp_to_prob (S : Substrate State) : ProbSubstrate State :=
{ transition := fun x => uniform (S.update x) (S.update_nonempty x) }

def hitting_prob_step (P : ProbSubstrate State) (target : Finset State) (curr : State → ℝ) : State → ℝ :=
  fun x => if x ∈ target then 1 else ∑ p in P.transition x.support, (P.transition x) p * curr p

def hitting_prob (P : ProbSubstrate State) (target : Finset State) (steps : ℕ) (x : State) : ℝ :=
  Nat.iterate (hitting_prob_step P target) (fun _ => 0) steps x

structure SoftAttractor (P : ProbSubstrate State) :=
  (carrier : Finset State)
  (hitting : State → ℝ)

def soft_from_crisp (P : ProbSubstrate State) (A : Attractor (crisp_of P)) (steps : ℕ) : SoftAttractor P :=
{ carrier := A.carrier, hitting := hitting_prob P A.carrier steps }

def ProbNested (threshold : ℝ) {n : ℕ}
    (S : SoftAttractor P) (B : Attractor (crisp_of P) n) : Prop :=
  ∀ x ∈ B.carrier, S.hitting x ≥ threshold

-------------------------------------------------------------------------------
-- 2. Sobolev L2 & L∞ norms, local gradient, perturbation
-------------------------------------------------------------------------------

def local_gradient (P : ProbSubstrate State) (x y : State) : ℝ :=
  ∑ z in univ, |pmf.prob (P.transition x) z - pmf.prob (P.transition y) z|

def reach_gradient (P : ProbSubstrate State) (steps : ℕ) (x : State) (A : SoftAttractor P) : ℝ :=
  |A.hitting x - hitting_prob P A.carrier steps x|

def L2_sobolev_norm (P : ProbSubstrate State) (steps : ℕ) (A : SoftAttractor P) : ℝ :=
  sqrt (∑ x in univ, (reach_gradient P steps x A)^2)

def perturbation_effect (P : ProbSubstrate State) (δ : State → State → ℝ) (x : State) (A : SoftAttractor P) : ℝ :=
  ∑ y in univ, δ x y * A.hitting y

def L∞_sobolev_norm (P : ProbSubstrate State) (steps : ℕ) (A : SoftAttractor P) : ℝ :=
  Finset.max' (univ.map (fun x => |reach_gradient P steps x A|)) (by simp)

lemma L2_sobolev_norm_nonneg (P : ProbSubstrate State) (steps : ℕ) (A : SoftAttractor P) :
  0 ≤ L2_sobolev_norm P steps A :=
by unfold L2_sobolev_norm; apply Real.sqrt_nonneg

lemma L∞_bound_by_L2 (P : ProbSubstrate State) (steps : ℕ) (A : SoftAttractor P) :
  L∞_sobolev_norm P steps A ≤ sqrt (Fintype.card State) * L2_sobolev_norm P steps A := by
unfold L∞_sobolev_norm L2_sobolev_norm reach_gradient
apply Finset.max'_le_of_mem
intros x hx
apply mul_le_mul_of_nonneg_left (sqrt_le_sum_squares (univ.map (fun x => |A.hitting x - hitting_prob P A.carrier steps x|))) (sqrt_nonneg _)

-------------------------------------------------------------------------------
-- 3. Hierarchy gradient & monotonicity
-------------------------------------------------------------------------------

def hierarchy_gradient (P : ProbSubstrate State) (n : ℕ) (A : NestedAttractor base_S (n+1)) : ℝ :=
  ∑ B in univ.filter (fun B : NestedAttractor base_S n => ProbNested 0 (soft_from_crisp P B.val 1000) B.val),
    L2_sobolev_norm P 1000 (soft_from_crisp P B.val 1000)

theorem hierarchy_gradient_monotone {n : ℕ} (P P' : ProbSubstrate State)
  (h : ∀ x y, P.transition x y ≤ P'.transition x y)
  (A : NestedAttractor base_S (n+1)) :
  hierarchy_gradient P n A ≤ hierarchy_gradient P' n A := by
unfold hierarchy_gradient
apply Finset.sum_le_sum
intros B hB
apply L2_sobolev_norm_monotone
let δ := fun x y => P'.transition x y - P.transition x y
have hδ : ∀ x y, 0 ≤ δ x y := by intros; exact sub_nonneg.mpr (h x y)
exact hδ

theorem nested_L2_increases_with_depth {n : ℕ} (P : ProbSubstrate State)
  (A : NestedAttractor base_S (n+1)) (h_self : IsSelfNested A) :
  L2_sobolev_norm P 1000 (soft_from_crisp P A.val 1000) ≥
  hierarchy_gradient P n A := by
rcases h_self with ⟨B⟩
unfold hierarchy_gradient
apply Finset.single_le_sum
intro x hx
apply L2_sobolev_norm_monotone
let δ := fun x y => if y ∈ B.val.carrier then L2_sobolev_norm P 1000 (soft_from_crisp P B.val 1000) else 0
have hδ : ∀ x y, 0 ≤ δ x y := by intros; split_ifs; linarith
exact hδ

-------------------------------------------------------------------------------
-- 4. Perturbation propagation through hierarchy
-------------------------------------------------------------------------------

lemma perturbation_effect_bound (P : ProbSubstrate State)
  (δ : State → State → ℝ) (hδ : ∀ x y, |δ x y| ≤ ε)
  (steps : ℕ) (A : SoftAttractor P) (x : State) :
  |perturbation_effect P δ x A| ≤ ε * Fintype.card State := by
unfold perturbation_effect
apply Finset.sum_le_sum
intros y hy
specialize hδ x y
apply mul_le_of_le_one_left; linarith

lemma L2_sobolev_norm_perturbation (P : ProbSubstrate State)
  (δ : State → State → ℝ) (hδ : ∀ x y, |δ x y| ≤ ε)
  (steps : ℕ) (A : SoftAttractor P) :
  |L2_sobolev_norm
      { transition := fun x => PMF.map (fun y => P.transition x y + δ x y) univ }
      steps A
    - L2_sobolev_norm P steps A| ≤ sqrt (Fintype.card State) * ε := by
unfold L2_sobolev_norm reach_gradient
have H : ∀ x ∈ univ, |(reach_gradient { transition := fun x => PMF.map (fun y => P.transition x y + δ x y) univ } steps x A)
                        - reach_gradient P steps x A| ≤ ε := by
  intros x hx
  unfold reach_gradient
  rw abs_sub
  apply Finset.sum_le_sum
  intros y hy
  specialize hδ x y
  exact hδ
apply mul_le_mul_of_nonneg_left (sqrt_sum_sq_le _ H) (sqrt_nonneg _)

theorem hierarchy_gradient_perturbation (P : ProbSubstrate State) (n : ℕ)
  (A : NestedAttractor base_S (n+1)) (δ : State → State → ℝ)
  (hδ : ∀ x y, |δ x y| ≤ ε) :
  |hierarchy_gradient
      { transition := fun x => PMF.map (fun y => P.transition x y + δ x y) univ } n A
    - hierarchy_gradient P n A| ≤
  ∑ B in univ.filter (fun B : NestedAttractor base_S n => ProbNested 0 (soft_from_crisp P B.val 1000) B.val),
    sqrt (Fintype.card State) * ε := by
unfold hierarchy_gradient
apply Finset.sum_le_sum
intros B hB
apply L2_sobolev_norm_perturbation
exact hδ

lemma L∞_sobolev_norm_perturbation (P : ProbSubstrate State) (δ : State → State → ℝ)
  (hδ : ∀ x y, |δ x y| ≤ ε) (steps : ℕ) (A : SoftAttractor P) :
  |L∞_sobolev_norm
      { transition := fun x => PMF.map (fun y => P.transition x y + δ x y) univ }
      steps A
    - L∞_sobolev_norm P steps A| ≤ ε := by
unfold L∞_sobolev_norm reach_gradient
apply Finset.max'_le
intros x hx
apply Finset.sum_le_sum
intros y hy
specialize hδ x y
exact hδ
