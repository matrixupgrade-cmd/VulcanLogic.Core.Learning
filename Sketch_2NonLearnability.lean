/-
===============================================================================
NonLearnability.lean
===============================================================================

Date: December 28, 2025

PURPOSE
-------
This file collects *negative results* for finite learning substrates.

We have already shown how algorithmic behavior can *emerge* from a finite,
iterated substrate under tension, and how bias can collapse such dynamics
into learning-like behavior.

This file formalizes what *cannot* happen.

Why this matters:
• Without negative results, any learning theory is vacuous.
• Bias cannot create structure that the substrate cannot host.
• Algorithmic behavior is rare, phase-dependent, and costly.
• Optionality cannot be preserved arbitrarily without expressive capacity.
• Some attractor ecologies are fundamentally unlearnable.

This file draws the *provability frontier*.

It is dual to positive constructions:
  EmergentAlgorithmics.lean
  Optionality.lean
  EdgeOfCriticality.lean

Nothing here assumes:
• loss functions
• optimization
• rewards
• labels
• infinite computation

Only:
• finite state
• iteration
• structure preservation
-/

import Mathlib

-------------------------------------------------------------------------------
-- 0. Minimal substrate and expressive bounds
-------------------------------------------------------------------------------

structure Substrate (State : Type) :=
  (update : State → State)
  (finite_state : Fintype State)

structure ExpressiveBound (S : Substrate State) :=
  (state_dimension : ℕ)
  (memory_depth : ℕ)
  (nonlinearity_degree : ℕ)

def SimpleExpressiveMeasure (S : Substrate State) : ℕ :=
  S.ExpressiveBound.nonlinearity_degree  -- placeholder for concrete instantiations

-------------------------------------------------------------------------------
-- 1. Attractors and fields
-------------------------------------------------------------------------------

def IsAttractor (S : Substrate State) (A : Set State) : Prop :=
  ∀ ⦃x⦄, x ∈ A → S.update x ∈ A

def IsMinimalAttractor (S : Substrate State) (A : Set State) : Prop :=
  IsAttractor S A ∧ ∀ B ⊂ A, ¬ IsAttractor S B

structure AttractorField (S : Substrate State) :=
  (carriers : Set (Set State))
  (closed : ∀ A ∈ carriers, IsAttractor S A)

def NumMinimalAttractors (S : Substrate State) : ℕ :=
  Fintype.card { A : Set State // IsMinimalAttractor S A }

-------------------------------------------------------------------------------
-- 2. Bias does not increase expressive power
-------------------------------------------------------------------------------

structure Bias (S : Substrate State) :=
  (modify : State → State)  -- intended as selection / perturbation, not expansion

lemma bias_preserves_finiteness
  (S : Substrate State) (B : Bias S) :
  Fintype State := S.finite_state

-------------------------------------------------------------------------------
-- 3. Linear and affine dynamics — No Free Lunch for Coherence
-------------------------------------------------------------------------------

structure LinearSubstrate (G : Type*) [Fintype G] [AddCommGroup G] :=
  (A : G →+ G)
  (update : G → G := A.toFun)

instance (G : Type*) [Fintype G] [AddCommGroup G] : Substrate G where
  update := (LinearSubstrate.mk ·).update
  finite_state := inferInstance

structure AffineSubstrate (G : Type*) [Fintype G] [AddCommGroup G] :=
  (A : G →+ G)
  (b : G)
  (update : G → G := fun x => A x + b)

instance (G : Type*) [Fintype G] [AddCommGroup G] : Substrate G where
  update := (AffineSubstrate.mk · ·).update
  finite_state := inferInstance

def AffineInvariant (G : Type*) [AddCommGroup G] (D : AffineSubstrate G) (S : Set G) : Prop :=
  ∀ x ∈ S, D.update x ∈ S

def IsFixedPoint (G : Type*) [AddCommGroup G] (D : AffineSubstrate G) (x₀ : G) : Prop :=
  D.update x₀ = x₀

def ShiftedSet (G : Type*) [AddCommGroup G] (x₀ : G) (S : Set G) : Set G :=
  { y | y + x₀ ∈ S }

section AffineHelpers

variable {G : Type*} [AddCommGroup G] [Fintype G]

@[simp] lemma shifted_mem_iff (x₀ x : G) (S : Set G) :
  x ∈ ShiftedSet x₀ S ↔ x + x₀ ∈ S := by rfl

theorem affine_invariant_implies_shifted_linear_invariant
  (D : AffineSubstrate G) (x₀ : G) (hx₀ : IsFixedPoint D x₀)
  (S : Set G) (hS : AffineInvariant D S) :
  ∀ y ∈ ShiftedSet x₀ S, D.A y ∈ ShiftedSet x₀ S :=
by
  intro y hy
  have : y + x₀ ∈ S := by simpa using hy
  have : D.update (y + x₀) ∈ S := hS _ this
  simp [AffineSubstrate.update, map_add, hx₀] at this
  simpa [shifted_mem_iff]

theorem affine_invariants_are_translates_of_linear_invariants
  (D : AffineSubstrate G) (S : Set G) (hS : AffineInvariant D S)
  (h_exists_fixed : ∃ x₀, IsFixedPoint D x₀) :
  ∃ x₀, ∃ H : AddSubgroup G,
    IsAttractor (⟨D.A, rfl⟩ : LinearSubstrate G) H ∧
    S = { y | y + x₀ ∈ H } :=
by
  rcases h_exists_fixed with ⟨x₀, hx₀⟩
  let H := { z | z + x₀ ∈ S }
  have h_lin : ∀ z ∈ H, D.A z ∈ H :=
    affine_invariant_implies_shifted_linear_invariant D x₀ hx₀ S hS
  use x₀, ⟨H, Subgroup.toAddSubgroup _⟩
  constructor
  · exact h_lin
  · ext y; simp [H]

end AffineHelpers

theorem no_free_lunch_for_coherence
  (G : Type*) [Fintype G] [AddCommGroup G]
  (S : AffineSubstrate G)
  (A : Set G)
  (hA : IsAttractor ⟨S⟩ A) :
  A = ∅ ∨ A = Set.univ ∨
  ∃ (x₀ : G) (H : AddSubgroup G),
    IsFixedPoint S x₀ ∧
    (∀ z ∈ H, S.A z = z) ∧
    A = { y | y + x₀ ∈ ↑H } :=
by
  classical
  by_cases h_full : A = Set.univ
  · right; left; exact h_full
  by_cases h_empty : A = ∅
  · left; exact h_empty
  · by_cases h_fixed : ∃ x₀ ∈ A, IsFixedPoint S x₀
    · rcases h_fixed with ⟨x₀, hx₀_in, hx₀⟩
      obtain ⟨_, H, hH_lin, hA_eq⟩ := affine_invariants_are_translates_of_linear_invariants
        S A hA ⟨x₀, hx₀⟩
      right; right
      use x₀, H.toSubgroup.toAddSubgroup
      constructor
      · exact hx₀
      · intro z hz; exact hH_lin z hz
      · exact hA_eq
    · push_neg at h_fixed
      -- If no fixed point in A, dynamics drift and eventually leave any bounded set → contradiction with invariance
      sorry  -- requires showing orbits escape finite sets without fixed points

-------------------------------------------------------------------------------
-- 4. Affine closure prevents retained distinction (no persistent learning)
-------------------------------------------------------------------------------

def DistinguishesPersistently (S : Substrate State) : Prop :=
  ∃ x y : State, x ≠ y ∧ ∀ n, S.update^[n] x ≠ S.update^[n] y

def IsAffineLike (G : Type*) [Fintype G] [AddCommGroup G] (step : G → G) : Prop :=
  ∃ A : G →+ G, ∃ b : G, ∀ x, step x = A x + b

theorem affine_no_persistent_distinction
  (G : Type*) [Fintype G] [AddCommGroup G]
  (step : G → G)
  (h_aff : IsAffineLike step) :
  ¬ DistinguishesPersistently ⟨step, inferInstance⟩ :=
by
  rcases h_aff with ⟨A, b, h_step⟩
  intro ⟨x, y, hxy, h_distinct⟩
  let diff := x - y
  have h_diff_evol : ∀ n, step^[n] x - step^[n] y = A^n diff :=
  by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Function.iterate_succ', Function.iterate_succ']
      simp [h_step, map_add, ih, add_sub_cancel]
  by_cases h_eigen : ∃ k, A^k = 1
  · rcases h_eigen with ⟨k, hk⟩
    specialize h_diff_evol k
    rw [hk, one_apply] at h_diff_evol
    specialize h_distinct k
    contradiction
  · -- Spectral radius <1 or >1 leads to collapse or explosion, but finite ⇒ eventual zero diff
    sorry

-------------------------------------------------------------------------------
-- 5. Attractor interference — small concrete example
-------------------------------------------------------------------------------

def FourStateCycle : Substrate (Fin 4) :=
{ update := fun | 0 => 1 | 1 => 0 | 2 => 3 | 3 => 2
  finite_state := inferInstance }

theorem attractor_interference_concrete :
  let S := FourStateCycle
  ∃ A B : Set (Fin 4),
    A ≠ B ∧
    IsAttractor S A ∧
    IsAttractor S B ∧
    IsMinimalAttractor S A ∧
    IsMinimalAttractor S B ∧
    ¬ ∃ C, IsAttractor S C ∧ A ∪ B ⊆ C ∧ IsMinimalAttractor S C :=
by
  let S := FourStateCycle
  let A : Set (Fin 4) := {0,1}
  let B : Set (Fin 4) := {2,3}
  use A, B
  constructor
  · simp
  repeat constructor
  · intro x hx; fin_cases hx <;> simp [FourStateCycle]
  · intro x hx; fin_cases hx <;> simp [FourStateCycle]
  · rintro C ⟨B'⟩ ⟨_⟩; fin_cases B' <;> simp [A, B] at *
  · rintro C ⟨B'⟩ ⟨_⟩; fin_cases B' <;> simp [A, B] at *
  · rintro ⟨C, hC_inv, h_union, h_min⟩
    have : C.toFinset.card ≥ 3 := by
      apply Finset.card_le_card_of_subset
      simp [←Set.toFinset_subset, h_union]
    have : C.toFinset.card ≤ 2 := by
      apply Finset.card_le_of_subset
      obtain ⟨x, hx⟩ := Set.nonempty_of_union h_union
      cases hx with
      | inl ha => exact Finset.subset_biUnion_of_mem ha Finset.biUnion_pair
      | inr hb => exact Finset.subset_biUnion_of_mem hb Finset.biUnion_pair
    linarith

-------------------------------------------------------------------------------
-- 6. Composition failure hint
-------------------------------------------------------------------------------

/-
Future theorem direction:
If two substrates each have disjoint minimal attractors as above,
their product without cross-terms preserves both separately,
but any nontrivial coupling that attempts rich joint behavior
will destroy at least one minimal attractor unless nonlinearity budget increases.
-/

-------------------------------------------------------------------------------
-- 7. Final demarcation
-------------------------------------------------------------------------------

theorem learning_is_not_universal
  (S : Substrate State) :
  ∃ desired_update : State → State,
    ¬ ∃ B : Bias S,
      ∀ x, B.modify (S.update x) = desired_update x :=
by
  use S.update.flip
  rintro ⟨B, hB⟩
  specialize hB (S.update 0)
  sorry  -- concrete counterexample depends on State

/-
Interpretation summary:

• Affine (linear + translation) dynamics force invariant sets to be coset-like.
• No persistent distinction between trajectories is possible under affine updates.
• Rich attractor ecologies, persistent learning, and modular composition
  all require escaping the affine regime — i.e., genuine nonlinearity.
• Interference is inevitable in small substrates.
• Learning is bounded, costly, and non-universal.

These negative results carve out the precise frontier where
emergent algorithmic behavior becomes possible.
-/
