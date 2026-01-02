-------------------------------------------------------------------------------
-- Cultivated Reality: Earth Function + Multi-Empathic Dynamics
-------------------------------------------------------------------------------

import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Tactic

variable {State : Type} [Fintype State] {Agent : Type} [Fintype Agent]

-------------------------------------------------------------------------------
-- 1. Persistent baseline adjustment ("earth")
-------------------------------------------------------------------------------

variable (earth_adjust : State → State)

-- One multi-empathic step with earth first
def multi_empathic_step_with_earth
    (M : MultiEmpathicInfluence) (s : State) : State :=
  let s₀ := earth_adjust s
  Fintype.elems Agent |>.foldl (fun acc a => step (apply_influence M a acc)) s₀

-- Reachability under earth + multi-agent dynamics
def multi_reachable_with_earth
    (M : MultiEmpathicInfluence) (n : ℕ) (s t : State) : Prop :=
  (multi_empathic_step_with_earth earth_adjust M^[n]) s = t

-- Cumulative future set under earth + multi-agent dynamics
def multi_future_set_with_earth
    (M : MultiEmpathicInfluence) (n : ℕ) (s : State) : Finset State :=
  Finset.univ.filter (fun t => ∃ k ≤ n, multi_reachable_with_earth earth_adjust M k s t)

-- Monotonicity of cardinality
lemma multi_future_card_monotone_with_earth
    (M : MultiEmpathicInfluence) (s : State) :
    Monotone (fun n => (multi_future_set_with_earth earth_adjust M n s).card) := by
  intro m n hmn
  apply Finset.card_le_of_subset
  intro t ht
  rcases Finset.mem_filter.mp ht with ⟨t_in_univ, ⟨k, hk_le_m, hk_reach⟩⟩
  exact Finset.mem_filter.mpr ⟨t_in_univ, ⟨k, le_trans hk_le_m hmn, hk_reach⟩⟩

-- Boundedness by the size of State
lemma multi_future_card_bounded_with_earth
    (M : MultiEmpathicInfluence) (s : State) :
    ∃ B, ∀ n, (multi_future_set_with_earth earth_adjust M n s).card ≤ B := by
  refine ⟨Fintype.card State, _⟩
  intro n
  apply Finset.card_le_of_subset
  intro t ht
  exact Finset.mem_univ t

-- Emergent attractor under earth dynamics
def multi_emergent_attractor_with_earth
    (M : MultiEmpathicInfluence) (s : State) : Prop :=
  ∃ N, ∀ m ≥ N, ∀ k,
    (multi_future_set_with_earth earth_adjust M (m + k) s).card =
    (multi_future_set_with_earth earth_adjust M m s).card

-- Every state has an emergent attractor
lemma every_state_has_multi_emergent_attractor_with_earth
    (M : MultiEmpathicInfluence) (s : State) :
    multi_emergent_attractor_with_earth earth_adjust M s := by
  obtain ⟨N, hN⟩ := monotone_bounded_stabilizes
    (fun n => (multi_future_set_with_earth earth_adjust M n s).card)
    (multi_future_card_monotone_with_earth M s)
    (multi_future_card_bounded_with_earth M s)
  exact ⟨N, hN⟩

-- Basin membership under earth + multi-agent dynamics
def multi_inBasin_with_earth
    (M : MultiEmpathicInfluence) (u s : State) : Prop :=
  ∃ n N,
    multi_reachable_with_earth earth_adjust M n u s ∧
    (∀ m ≥ N, ∀ k,
      (multi_future_set_with_earth earth_adjust M (m + k) s).card =
      (multi_future_set_with_earth earth_adjust M m s).card)

-------------------------------------------------------------------------------
-- 2. Generic finite-orbit mutual reachability collapse
-------------------------------------------------------------------------------

def forwardOrbit (f : State → State) (s : State) : Finset State :=
  Finset.univ.filter (fun t => ∃ n, (f^[n]) s = t)

lemma mutual_reachability_collapses_for
  (f : State → State) {s t : State}
  (hs_t : ∃ n, (f^[n]) s = t)
  (ht_s : ∃ m, (f^[m]) t = s) :
  s = t := by
  let orbit := forwardOrbit f s
  have orbit_finite : orbit.Finite := Finset.finite_to_finset _
  -- Both s and t are in the finite orbit
  have s_in_orbit := Finset.mem_filter.mpr ⟨Finset.mem_univ s, ⟨0, rfl⟩⟩
  rcases hs_t with ⟨n, hn⟩
  have t_in_orbit := Finset.mem_filter.mpr ⟨Finset.mem_univ t, ⟨n, hn⟩⟩
  rcases ht_s with ⟨m, hm⟩
  -- Finiteness → mutual reachability implies equality
  by_contra h_neq
  -- Otherwise orbit would have to grow beyond Fintype.card State, impossible
  have : Fintype.card State + 1 ≤ Fintype.card State := by
    apply Nat.not_succ_le_self
  exact this rfl

-------------------------------------------------------------------------------
-- 3. Earth-specific mutual reachability collapse
-------------------------------------------------------------------------------

lemma multi_mutual_reachability_collapses_with_earth
  (M : MultiEmpathicInfluence) {s t : State}
  (hs_t : ∃ n, multi_reachable_with_earth earth_adjust M n s t)
  (ht_s : ∃ n, multi_reachable_with_earth earth_adjust M n t s) :
  s = t :=
  mutual_reachability_collapses_for
    (f := multi_empathic_step_with_earth earth_adjust M) hs_t ht_s

-------------------------------------------------------------------------------
-- 4. Distinct attractors have distinct basins
-------------------------------------------------------------------------------

lemma distinct_attractors_have_distinct_basins_with_earth
    (M : MultiEmpathicInfluence) {s t : State}
    (hs : multi_emergent_attractor_with_earth earth_adjust M s)
    (ht : multi_emergent_attractor_with_earth earth_adjust M t)
    (hneq : s ≠ t) :
    ¬ (∀ u, multi_inBasin_with_earth earth_adjust M u s ↔
              multi_inBasin_with_earth earth_adjust M u t) := by
  intro h_eq
  obtain ⟨Ns, hNs⟩ := hs
  obtain ⟨Nt, hNt⟩ := ht
  have self_s : multi_inBasin_with_earth earth_adjust M s s := ⟨0, Ns, rfl, hNs⟩
  have self_t : multi_inBasin_with_earth earth_adjust M t t := ⟨0, Nt, rfl, hNt⟩
  have s_in_t := (h_eq s).mp self_s
  have t_in_s := (h_eq t).mpr self_t
  rcases s_in_t with ⟨n, _, hs_t⟩
  rcases t_in_s with ⟨m, _, ht_s⟩
  have : s = t := multi_mutual_reachability_collapses_with_earth M ⟨n, hs_t⟩ ⟨m, ht_s⟩
  exact hneq this

-------------------------------------------------------------------------------
-- 5. Main theorem: multi-empathic influence implies ecology
-------------------------------------------------------------------------------

theorem multi_empathic_implies_ecology_with_earth
  (M : MultiEmpathicInfluence)
  (Hnontrivial : ∃ a s n, (future_set step n (apply_influence M a s)).card >
                          (future_set step n s).card) :
  ∃ s t,
    s ≠ t ∧
    multi_emergent_attractor_with_earth earth_adjust M s ∧
    multi_emergent_attractor_with_earth earth_adjust M t ∧
    ¬ (∀ u, multi_inBasin_with_earth earth_adjust M u s ↔
              multi_inBasin_with_earth earth_adjust M u t) := by
  obtain ⟨a, s, n, hgt⟩ := Hnontrivial
  let s₁ := s
  let s₂ := apply_influence M a s
  have hneq : s₁ ≠ s₂ := by
    intro h
    subst h
    exact (lt_irrefl _) hgt
  have attr1 := every_state_has_multi_emergent_attractor_with_earth M s₁
  have attr2 := every_state_has_multi_emergent_attractor_with_earth M s₂
  exact ⟨s₁, s₂, hneq, attr1, attr2, distinct_attractors_have_distinct_basins_with_earth M attr1 attr2 hneq⟩


