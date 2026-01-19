import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Data.List.Defs
import Mathlib.Data.Function.Iterate

namespace FiniteSystem

-- === Core structure ===
structure FiniteSystem (α : Type*) [Fintype α] where
  T : α → α

variable {α : Type*} [Fintype α] (sys : FiniteSystem α)

-- Iteration
def iter (n : ℕ) (s : α) : α := sys.T^[n] s

lemma iter_zero (s : α) : iter 0 s = s := rfl
lemma iter_succ (n : ℕ) (s : α) : iter (n + 1) s = sys.T (iter n s) := rfl
lemma iter_add (m n : ℕ) (s : α) : iter (m + n) s = iter m (iter n s) := by
  induction m <;> simp [iter_succ, *, Nat.add_succ]

-- Every orbit eventually enters a cycle
lemma orbit_enters_cycle (s : α) : ∃ n m, n < m ∧ iter m s = iter n s := by
  classical
  let φ : ℕ → α := fun k ↦ iter k s
  let rng := Finset.range (Fintype.card α + 1)
  let imgs := rng.image φ
  have h_card_le : imgs.card ≤ Fintype.card α := Finset.card_image_le
  have h_lt : imgs.card < Fintype.card α + 1 := lt_of_le_of_lt h_card_le (Nat.lt_succ_self _)
  obtain ⟨i, j, h_ne, h_eq⟩ := Finset.exists_ne_map_eq_of_card_lt φ h_lt
  wlog h : i < j generalizing i j
  · exact this j i (Ne.symm h_ne.1) h_ne.2 (h.lt_or_lt.resolve_left h_ne.1.ne')
  exact ⟨i, j, h, h_eq⟩

-- === Stable Relational Invariant ===
structure StableRelationalInvariant where
  R : α → α → Prop
  N : ℕ
  stable : ∀ ⦃s₁ s₂ n⦄, n ≥ N → R s₁ s₂ → R (iter n s₁) (iter n s₂)

-- Canonical SRI: eventual future equivalence
def eventualFutureEquivalence : StableRelationalInvariant where
  R s₁ s₂ := ∃ k, iter k s₁ = iter k s₂
  N       := Fintype.card α
  stable n hn ⟨k, hk⟩ := ⟨k + n, by simp [← iter_add, hk]⟩

-- Non-triviality for the concrete Fin 5 example
lemma eventualFutureEquivalence_nontrivial_fin5 :
    ¬ ∀ a b : Fin 5, eventualFutureEquivalence.R a b := by
  intro h_universal
  let a := 0
  let b := 2
  have ha_ne_b : a ≠ b := by decide
  specialize h_universal a b
  obtain ⟨k, hk⟩ := h_universal

  have h0 : ∀ m, iter m 0 = 0 := by
    intro m
    induction m using Nat.strongInductionOn with
    | h m ih =>
      cases m
      · rfl
      · simp [iter_succ, exampleT, ih m.prop]

  have h2 : ∀ m, iter m 2 = 2 := by
    intro m
    induction m using Nat.strongInductionOn with
    | h m ih =>
      cases m
      · rfl
      · simp [iter_succ, exampleT, ih m.prop]

  have : iter k 0 = 0 := h0 k
  have : iter k 2 = 2 := h2 k
  rw [this, this] at hk
  exact ha_ne_b hk.symm

-- Heavenly Rules
structure HeavenlyRules where
  invariants : List StableRelationalInvariant

def sriEquivalence (rules : HeavenlyRules) (x y : α) : Prop :=
  ∀ r ∈ rules.invariants, r.R x y

def heavenlyPartition (rules : HeavenlyRules) : Set (Set α) :=
  { C | C.Nonempty ∧ ∀ x y ∈ C, sriEquivalence rules x y ∧
        ∀ z ∉ C, ¬ sriEquivalence rules x z }

def metaMap (rules : HeavenlyRules) (C : Set α) : Set α := sys.T '' C

-- Trichotomy
inductive LongTermStructure
| frozen
| cyclic
| partiallyOpen

deriving DecidableEq for LongTermStructure

def isFrozen (rules : HeavenlyRules) : Prop :=
  ∀ C ∈ heavenlyPartition rules, metaMap rules C ⊆ C

def classify (rules : HeavenlyRules) : LongTermStructure :=
  if isFrozen rules then .frozen else .partiallyOpen

-- Emergent rules = canonical SRI
def emergentHeavenlyRules : HeavenlyRules :=
  { invariants := [eventualFutureEquivalence] }

-- Partition sequence (evaluates relation at step n)
def partitionSequence (rules : HeavenlyRules) (n : ℕ) : Set (Set α) :=
  { C | C.Nonempty ∧ ∀ x y ∈ C, (∀ r ∈ rules.invariants, r.R (iter n x) (iter n y)) ∧
        ∀ z ∉ C, ¬ (∀ r ∈ rules.invariants, r.R (iter n x) (iter n z)) }

lemma partition_sequence_stabilizes (rules : HeavenlyRules) :
    ∃ N, ∀ n ≥ N, partitionSequence rules n = partitionSequence rules N := by
  classical
  let D := Fintype.card α
  use D
  intro n hn
  ext C
  constructor
  · intro hC
    obtain ⟨h_nonemp, h_equiv_n, h_not_out_n⟩ := hC
    constructor
    · exact h_nonemp
    · intro x y hx hy r hr
      have h_stable : ∀ s₁ s₂ m ≥ D, eventualFutureEquivalence.R s₁ s₂ → 
          ∀ k ≥ m, eventualFutureEquivalence.R (iter k s₁) (iter k s₂) := by
        intro s₁ s₂ m hm ⟨k, hk⟩ k' hk'
        use k + (k' - m)
        simp [← iter_add, hk]
      have h_same : eventualFutureEquivalence.R x y := by
        apply h_equiv_n x y hx hy r hr
      apply h_stable x y n hn h_same n hn r hr
    · intro z hz r hr
      apply h_not_out_n z hz r hr
  · intro hC
    obtain ⟨h_nonemp, h_equiv_n, h_not_out_n⟩ := hC
    constructor
    · exact h_nonemp
    · intro x y hx hy r hr
      have h_same : eventualFutureEquivalence.R x y := by
        apply h_equiv_n x y hx hy r hr
      obtain ⟨k, hk⟩ := h_same
      use k + n
      simp [← iter_add, hk]
    · intro z hz r hr
      apply h_not_out_n z hz r hr

-- Canonical frozen theorem
theorem canonical_sri_frozen [Nontrivial α] :
    classify emergentHeavenlyRules = .frozen := by
  unfold classify emergentHeavenlyRules
  simp only [isFrozen]
  intro C hC
  obtain ⟨h_nonemp, h_equiv, h_not⟩ := hC
  obtain ⟨x, hx⟩ := h_nonemp
  have h_image : ∀ s ∈ C, sys.T s ∈ C := by
    intro s hs
    have h_same : eventualFutureEquivalence.R x (sys.T s) := by
      obtain ⟨k, hk⟩ := h_equiv x s hx hs eventualFutureEquivalence (List.mem_singleton_self _)
      use k + 1
      simp [← iter_add, hk]
    apply h_equiv (sys.T s) x (by simp) hx eventualFutureEquivalence (List.mem_singleton_self _)
  simp [metaMap]
  exact Set.image_subset_iff.mpr h_image

-- === Fin 5 example ===
def exampleT : Fin 5 → Fin 5
  | 0 => 0
  | 1 => 0
  | 2 => 2
  | 3 => 4
  | 4 => 3

def exampleSys : FiniteSystem (Fin 5) := ⟨exampleT⟩

def exampleRules : HeavenlyRules := emergentHeavenlyRules

def basin0 : Set (Fin 5) := {0, 1}
def basin2 : Set (Fin 5) := {2}
def basin34 : Set (Fin 5) := {3, 4}

lemma example_partition_correct :
    heavenlyPartition exampleRules = {basin0, basin2, basin34} := by
  ext C
  constructor
  · intro hC
    obtain ⟨h_nonemp, h_equiv, h_not_out⟩ := hC
    obtain ⟨x, hx⟩ := h_nonemp
    fin_cases x
    · have h1 : 1 ∈ C := by
        apply h_equiv 0 1 hx
        simp [eventualFutureEquivalence]
        use 1; simp [iter_succ, exampleT]
      have h_only : C = basin0 := by
        ext y; constructor
        · intro hy; fin_cases y <;> [rfl | exact h1 | exact absurd rfl (h_not_out _ (by simp))]
        · rintro (rfl | rfl); exact hx; exact h1
      rw [h_only]
    · have h0 : 0 ∈ C := by
        apply h_equiv 1 0 hx
        simp [eventualFutureEquivalence]
        use 1; simp [iter_succ, exampleT]
      have h_only : C = basin0 := by
        ext y; constructor
        · intro hy; fin_cases y <;> [exact h0 | rfl | exact absurd rfl (h_not_out _ (by simp))]
        · rintro (rfl | rfl); exact h0; exact hx
      rw [h_only]
    · have h_only : C = basin2 := by
        ext y; constructor
        · intro hy; fin_cases y <;> [exact absurd rfl (h_not_out _ (by simp)) | rfl | exact absurd rfl (h_not_out _ (by simp))]
        · rintro rfl; exact hx
      rw [h_only]
    · have h4 : 4 ∈ C := by
        apply h_equiv 3 4 hx
        simp [eventualFutureEquivalence]
        use 1; simp [iter_succ, exampleT]
      have h_only : C = basin34 := by
        ext y; constructor
        · intro hy; fin_cases y <;> [exact absurd rfl (h_not_out _ (by simp)) | exact h4 | rfl]
        · rintro (rfl | rfl); exact hx; exact h4
      rw [h_only]
    · have h3 : 3 ∈ C := by
        apply h_equiv 4 3 hx
        simp [eventualFutureEquivalence]
        use 1; simp [iter_succ, exampleT]
      have h_only : C = basin34 := by
        ext y; constructor
        · intro hy; fin_cases y <;> [exact absurd rfl (h_not_out _ (by simp)) | exact h3 | rfl]
        · rintro (rfl | rfl); exact h3; exact hx
      rw [h_only]
  · rintro (rfl | rfl | rfl)
    · constructor
      · simp [basin0]
      · intro x y hx hy r hr
        simp [eventualFutureEquivalence] at *
        cases x <;> cases y <;> try exact ⟨1, rfl⟩
      · intro z hz; simp [basin0] at hz; fin_cases z <;> exact absurd rfl hz
    · constructor
      · simp [basin2]
      · intro x y hx hy r hr
        simp [eventualFutureEquivalence]
        use 0; rfl
      · intro z hz; simp [basin2] at hz; fin_cases z <;> exact absurd rfl hz
    · constructor
      · simp [basin34]
      · intro x y hx hy r hr
        simp [eventualFutureEquivalence] at *
        cases x <;> cases y <;> try exact ⟨1, rfl⟩
      · intro z hz; simp [basin34] at hz; fin_cases z <;> exact absurd rfl hz

lemma metaMap_invariant_example :
    metaMap exampleRules basin0 ⊆ basin0 ∧
    metaMap exampleRules basin2 ⊆ basin2 ∧
    metaMap exampleRules basin34 ⊆ basin34 := by
  simp [metaMap, exampleT, basin0, basin2, basin34]
  constructor <;> constructor <;> simp

theorem example_rules_frozen :
    classify exampleRules = .frozen := by
  unfold classify
  simp only
  intro C hC
  rw [example_partition_correct] at hC
  cases hC
  · exact (metaMap_invariant_example).1
  · exact (metaMap_invariant_example).2.1
  · exact (metaMap_invariant_example).2.2

#eval classify exampleRules  -- frozen

end FiniteSystem
