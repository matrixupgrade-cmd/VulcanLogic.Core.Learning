/-
===============================================================================
NonLearnability.lean
===============================================================================

Date: 2025

PURPOSE
-------

This file collects *negative results* for learning substrates.

We have already shown how algorithmic behavior can *emerge* from a finite,
iterated substrate under tension, and how bias can collapse such dynamics
into learning-like behavior.

What remains is to formalize what CANNOT happen.

Why this matters:

• Without negative results, any learning theory is vacuous.
• Bias cannot create structure that the substrate cannot host.
• Algorithmic behavior is rare, phase-dependent, and costly.
• Optionality cannot be preserved arbitrarily without expressive capacity.
• Some attractor ecologies are fundamentally unlearnable.

This file draws the *provability frontier*.

It is intentionally dual to positive constructions:
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

===============================================================================
-/

import Mathlib

-------------------------------------------------------------------------------
-- 1. Minimal substrate: iteration without semantics
-------------------------------------------------------------------------------

/--
A learning substrate is nothing more than a finite state space
with an iterated update rule.

We do NOT assume:
• optimality
• convergence
• gradients
• reward
• intelligence

Only iteration.
-/
structure Substrate (State : Type) :=
  (update : State → State)
  (finite_state : Fintype State)

-------------------------------------------------------------------------------
-- 2. Expressive bounds (what the substrate cannot exceed)
-------------------------------------------------------------------------------

/--
Expressive bounds describe what the substrate is capable of hosting.

These are NOT algorithms.
They are *invariants*.

Examples of future instantiations:
• graph degree bounds
• polynomial update order
• memory depth
• Lipschitz constants
• local interaction radius
-/
structure ExpressiveBound (S : Substrate State) :=
  (state_dimension : ℕ)
  (memory_depth : ℕ)
  (nonlinearity_degree : ℕ)

/--
Simple expressive measure: maximum polynomial degree of the update rule
(assuming State is a vector space or similar).
-/
def SimpleExpressiveMeasure (S : Substrate State) : ℕ :=
  S.ExpressiveBound.nonlinearity_degree  -- Placeholder; instantiate per substrate

-------------------------------------------------------------------------------
-- 3. Attractors and attractor ecologies
-------------------------------------------------------------------------------

/--
A self-attractor is simply a forward-invariant set.

No stability assumptions.
No convergence assumptions.
Just closure under iteration.
-/
def IsAttractor (S : Substrate State) (A : Set State) : Prop :=
  ∀ ⦃x⦄, x ∈ A → S.update x ∈ A

/--
An attractor field is a structured collection of attractors.

This represents:
• multiple learning trajectories
• coexisting strategies
• interacting basins

We deliberately avoid assuming trees or graphs.
-/
structure AttractorField (S : Substrate State) :=
  (carriers : Set (Set State))
  (closed : ∀ A ∈ carriers, IsAttractor S A)

/--
A minimal attractor is an attractor with no proper subset that is also an attractor.
-/
def IsMinimalAttractor (S : Substrate State) (A : Set State) : Prop :=
  IsAttractor S A ∧ ∀ B : Set State, B ⊂ A → ¬ IsAttractor S B

/--
Number of minimal attractors in the substrate.
-/
def NumMinimalAttractors (S : Substrate State) : ℕ :=
  Fintype.card { A : Set State // IsMinimalAttractor S A }

-------------------------------------------------------------------------------
-- 4. Bias does not increase expressive power
-------------------------------------------------------------------------------

/--
A bias modifies the update rule but does not expand the state space.

This encodes the core principle:
BIAS SELECTS — IT DOES NOT CREATE.
-/
structure Bias (S : Substrate State) :=
  (modify : State → State)

/--
Bias preserves finiteness.

This trivial lemma is conceptually important:
no amount of bias gives you new degrees of freedom.
-/
lemma bias_preserves_finiteness
  (S : Substrate State) (B : Bias S) :
  Fintype State :=
S.finite_state

-------------------------------------------------------------------------------
-- 5. EXPRESSIVE THRESHOLD THEOREM
-------------------------------------------------------------------------------
-- Some attractor fields are unlearnable by bounded substrates
-------------------------------------------------------------------------------

/--
Predicate capturing the idea that an attractor field
exceeds the expressive capacity of a substrate.

Instantiated via number of minimal attractors exceeding a bound.
-/
def ExceedsCapacity
  (E : ExpressiveBound S)
  (F : AttractorField S) : Prop :=
  NumMinimalAttractors S > 2 ^ E.nonlinearity_degree  -- Example instantiation

/--
EXPRESSIVE THRESHOLD THEOREM

There exist attractor ecologies that no bias can make learnable
on substrates below a certain expressive threshold.

This is the geometric analog of:
• VC dimension lower bounds
• circuit complexity lower bounds

Failure is structural, not statistical.

Here we provide a basic version: number of minimal attractors is bounded by exponential in nonlinearity degree.
-/
theorem expressive_threshold_basic
  (S : Substrate State)
  (E : ExpressiveBound S)
  (h : SimpleExpressiveMeasure S ≤ k) :
  NumMinimalAttractors S ≤ 2 ^ k := by
  -- Proof sketch: In a finite state space with update of degree ≤ k,
  -- the dynamics can be modeled as a polynomial map over a field,
  -- and the number of invariant sets is bounded by the variety dimension.
  -- Actual proof would use algebraic geometry or graph theory bounds.
  sorry  -- Replace with full proof when ready

-------------------------------------------------------------------------------
-- 6. NO FREE LUNCH FOR COHERENCE
-------------------------------------------------------------------------------
-- Chaos and retained complexity require nonlinearity
-------------------------------------------------------------------------------

/--
Affine substrate: linear updates over a module.
-/
structure AffineSubstrate (α : Type*) [Fintype α] [AddCommGroup α] [Module ℚ α] :=
  (A : α →ₗ[ℚ] α)
  (b : α)
  (update : α → α := fun x => A x + b)

/--
Coerce AffineSubstrate to Substrate.
-/
instance : Substrate α for AffineSubstrate α :=
  { update := self.update, finite_state := inferInstance }

/--
Predicate for substrates that are "too linear": here, affine.
-/
def LinearLike (S : Substrate State) : Prop :=
  ∃ α [Fintype α] [AddCommGroup α] [Module ℚ α],
    Nonempty (AffineSubstrate α) ∧ S.update = (Classical.choice ‹_›).update

/--
NO FREE LUNCH FOR COHERENCE

Linear or weakly nonlinear substrates cannot host
retained chaotic or richly structured attractors.

Coherence has a cost.

Proof: Over finite abelian groups with affine updates, invariant sets are cosets.
-/
theorem no_free_lunch_for_coherence
  (S : Substrate State)
  (h : LinearLike S) :
  ∀ A : Set State,
    IsAttractor S A →
    (A = ∅ ∨ A = Set.univ ∨ ∃ H : AddSubgroup State, A = AddCoset H some_element) := by
  intro A hA
  obtain ⟨α, _, _, _, ⟨AS⟩, h_up⟩ := h
  -- Rewrite update as affine
  rw [h_up] at hA
  -- Invariant under x ↦ A x + b implies A is union of cosets of ker(A - id)
  -- But for simplicity, in finite case, only trivial or full if irreducible, else cosets.
  sorry  -- Full proof: use linear algebra over modules

-------------------------------------------------------------------------------
-- 7. OPTIONALITY COLLAPSE BOUND
-------------------------------------------------------------------------------
-- You cannot stay liquid forever
-------------------------------------------------------------------------------

/--
Optionality depth measures how many viable futures remain accessible.

Here: size of reachable set after t steps, abstracted.
-/
def ReachableSetSize (S : Substrate State) (x0 : State) (t : ℕ) : ℕ :=
  Fintype.card { y : State // ∃ k ≤ t, y = S.update^[k] x0 }

/--
Optionality depth: maximum over starts of reachable size at depth t.
-/
def OptionalityDepth (S : Substrate State) (t : ℕ) : ℕ :=
  Finset.max (Finset.univ.image fun x0 => ReachableSetSize S x0 t)

/--
OPTIONALITY COLLAPSE THEOREM

Below a critical expressive threshold, deep optionality
cannot be preserved indefinitely.

Liquid behavior has a price.

In finite states, trivially bounded, but with local rules: linear growth.
-/
theorem optionality_collapse_local
  (S : Substrate State)
  (h_local : ∀ x, S.update x depends_only_on_neighborhood_of_radius r) :  -- Assume graph substrate
  ∃ c : ℕ,
    ∀ t, OptionalityDepth S t ≤ c * t := by
  -- Proof: In bounded-degree graphs or local CAs, information propagates at speed r,
  -- so reachable diameter ≤ r t, volume ≤ exp(r t) in infinite, but in finite: linear if sparse.
  sorry

-------------------------------------------------------------------------------
-- 8. ATTRACTOR INTERFERENCE THEOREM
-------------------------------------------------------------------------------
-- Joint learnability failure
-------------------------------------------------------------------------------

/--
Two attractors interfere if retaining one
destroys access to the other.
-/
def Interferes (S : Substrate State) (A B : Set State) : Prop :=
  ¬ ∃ C : Set State, IsAttractor S C ∧ A ∪ B ⊆ C ∧ IsMinimalAttractor S C

/--
Example 4-state substrate with disjoint cycles.
-/
def FourStateSubstrate : Substrate (Fin 4) :=
  let update : Fin 4 → Fin 4
  | 0 => 1
  | 1 => 0
  | 2 => 3
  | 3 => 2
  { update := update, finite_state := inferInstance }

/--
ATTRACTOR INTERFERENCE

Some attractors are individually realizable
but jointly impossible to retain.

This explains:
• catastrophic interference
• curriculum dependence
• multitask failure
-/
theorem attractor_interference_four_state :
  let S := FourStateSubstrate
  ∃ A B : Set (Fin 4),
    IsAttractor S A ∧
    IsAttractor S B ∧
    Interferes S A B ∧
    ¬ ∃ B : Bias S, ∃ C, IsAttractor S C ∧ A ∪ B ⊆ C := by
  intro S
  let A : Set (Fin 4) := {0,1}
  let B : Set (Fin 4) := {2,3}
  use A, B
  split
  · intro x hx; cases hx <;> simp [S]
  · intro x hx; cases hx <;> simp [S]
  · intro ⟨C, hC, hAB⟩
    -- Show no minimal C containing both: graph is disconnected
    sorry
  · intro ⟨bias⟩ ⟨C⟩ ⟨hC⟩ ⟨hAB⟩
    -- Bias can't add edges if it only selects/perms; assume bias model limits
    sorry

-------------------------------------------------------------------------------
-- 9. FINAL DEMARCATION THEOREM
-------------------------------------------------------------------------------

/--
LEARNING IS NOT UNIVERSAL

There exist behaviors that no bias can realize
on a given substrate.

This is the boundary of learning.
-/
theorem learning_is_not_universal
  (S : Substrate State) :
  ∃ behavior : State → State,  -- Some desired update
    ¬ ∃ bias : Bias S, ∀ x, (bias.modify x) = behavior x := by
  -- Trivial: pick behavior with higher complexity than S.update
  use fun x => x  -- Identity if S is not identity, etc.
  sorry

-------------------------------------------------------------------------------
-- 10. COMPOSITION FAILURE THEOREM (Braiding #2 and #3)
-------------------------------------------------------------------------------

/--
Substrate composition: simple union with cross-terms.
-/
def ComposeSubstrates (S1 : Substrate State1) (S2 : Substrate State2) : Substrate (State1 × State2) :=
  { update := fun ⟨x1, x2⟩ => ⟨S1.update x1, S2.update x2⟩,  -- No cross yet; add if needed
    finite_state := inferInstance }

/--
COMPOSITION FAILURE

Some pairs of converged substrates cannot be composed without
losing one attractor.

Negative for modularity.
-/
theorem composition_failure
  (S1 : Substrate State1) (S2 : Substrate State2)
  (A1 : Set State1) (A2 : Set State2)
  (hA1 : IsAttractor S1 A1)
  (hA2 : IsAttractor S2 A2) :
  ∃ coupling,  -- Some bad coupling
    let SC := coupling S1 S2
    ¬ ∃ AC : Set (State1 × State2),
      IsAttractor SC AC ∧
      (∀ x1 ∈ A1, ∀ x2, ⟨x1, x2⟩ ∈ AC) ∧
      (∀ x2 ∈ A2, ∀ x1, ⟨x1, x2⟩ ∈ AC) := by
  -- Use interfering attractors from earlier
  sorry
