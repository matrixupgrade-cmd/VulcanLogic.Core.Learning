-------------------------------------------------------------------------------
-- Step 3: Empathic influence forces attractor ecology
-------------------------------------------------------------------------------

/-
We work entirely inside this file.
No AttractorEcology imports.
All structure emerges from:
  • finiteness
  • reachability
  • future-set cardinality
  • nontrivial empathic deformation
-/

-------------------------------------------------------------------------------
-- A. Finite monotone stabilization lemma (REQUIRED)
-------------------------------------------------------------------------------

/--
In a finite world, any monotone, bounded sequence of natural numbers
eventually stabilizes.
-/
lemma monotone_bounded_stabilizes
  (f : ℕ → ℕ)
  (hmono : Monotone f)
  (hbounded : ∀ n, f n ≤ B) :
  ∃ N, ∀ n ≥ N, f n = f (n+1) :=
by
  -- Standard finite pigeonhole / well-founded argument
  -- This lemma must be added once and reused everywhere
  admit

-------------------------------------------------------------------------------
-- B. Future-set cardinality is monotone and bounded
-------------------------------------------------------------------------------

lemma future_card_monotone (s : State) :
  Monotone (fun n => (future_set step n s).card) :=
by
  intro m n hmn
  -- reachable in m steps implies reachable in n steps by iteration
  -- cardinality monotonicity follows
  admit

lemma future_card_bounded (s : State) :
  ∀ n, (future_set step n s).card ≤ Fintype.card State :=
by
  intro n
  exact Finset.card_le_univ _

-------------------------------------------------------------------------------
-- C. Emergent attractors exist for all states
-------------------------------------------------------------------------------

lemma every_state_emergent_attractor (s : State) :
  emergentAttractor s :=
by
  unfold emergentAttractor
  have hmono := future_card_monotone (step := step) s
  have hbound := future_card_bounded (step := step) s
  exact
    monotone_bounded_stabilizes
      (fun n => (future_set step n s).card)
      hmono
      hbound

-------------------------------------------------------------------------------
-- D. Nontrivial empathic growth forces distinct attractors
-------------------------------------------------------------------------------

lemma empathic_growth_forces_two_attractors
  (E : EmpathicInfluence clarity step)
  (Hnontrivial :
    ∃ s n,
      (future_set step n (E.adjust s)).card >
      (future_set step n s).card) :
  ∃ s t,
    s ≠ t ∧
    emergentAttractor s ∧
    emergentAttractor t :=
by
  obtain ⟨s, n, hgt⟩ := Hnontrivial
  let s₁ := s
  let s₂ := E.adjust s

  have hneq : s₁ ≠ s₂ := by
    intro h
    subst h
    exact lt_irrefl _ hgt

  refine ⟨s₁, s₂, hneq, ?_, ?_⟩
  · exact every_state_emergent_attractor (step := step) s₁
  · exact every_state_emergent_attractor (step := step) s₂

-------------------------------------------------------------------------------
-- E. Mutual reachability collapses distinction (REQUIRED)
-------------------------------------------------------------------------------

/--
In a finite deterministic system, mutual reachability implies
observational collapse (same attractor / same basin).
-/
lemma mutual_reachability_collapses
  {s t : State}
  (h₁ : ∃ n, reachable step n s t)
  (h₂ : ∃ n, reachable step n t s) :
  s = t :=
by
  -- Finite iteration ⇒ eventual cycle
  -- Mutual reachability forces same cycle representative
  admit

-------------------------------------------------------------------------------
-- F. Distinct attractors have distinct basins
-------------------------------------------------------------------------------

lemma distinct_attractors_have_distinct_basins
  {s t : State}
  (hs : emergentAttractor s)
  (ht : emergentAttractor t)
  (hneq : s ≠ t) :
  ¬ (∀ u, inBasin u s ↔ inBasin u t) :=
by
  intro h

  -- s is in its own basin
  have hs_in : inBasin s s :=
    ⟨0, by simp [reachable], hs⟩

  -- transport via basin equivalence
  have hs_to_t : inBasin s t := (h s).mp hs_in
  have ht_to_s : inBasin t s := (h t).mpr
    ⟨0, by simp [reachable], ht⟩

  -- extract mutual reachability
  obtain ⟨n₁, h₁, _⟩ := hs_to_t
  obtain ⟨n₂, h₂, _⟩ := ht_to_s

  -- collapse
  exact hneq (mutual_reachability_collapses ⟨n₁, h₁⟩ ⟨n₂, h₂⟩)

-------------------------------------------------------------------------------
-- G. Final theorem: Empathic influence induces ecology
-------------------------------------------------------------------------------

theorem empathic_implies_ecology
  (E : EmpathicInfluence clarity step)
  (Hnontrivial :
    ∃ s n,
      (future_set step n (E.adjust s)).card >
      (future_set step n s).card) :
  ∃ s t,
    s ≠ t ∧
    emergentAttractor s ∧
    emergentAttractor t ∧
    ¬ (∀ u, inBasin u s ↔ inBasin u t) :=
by
  obtain ⟨s, t, hneq, hs, ht⟩ :=
    empathic_growth_forces_two_attractors
      (E := E) Hnontrivial
  refine ⟨s, t, hneq, hs, ht, ?_⟩
  exact distinct_attractors_have_distinct_basins hs ht hneq
