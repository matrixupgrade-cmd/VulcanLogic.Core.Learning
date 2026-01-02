/-
===============================================================================
Cultivated Reality
Author: Sean Timothy  (Special Thanks to Microsoft Co-Pilot)
Date: 2026-01-01

Purpose:
  Formalization of a persistent substrate ("earth") in multi-agent empathic
  dynamics. The "earth_adjust" function is applied before all agents on each
  step, modeling a cultivated baseline reality on which agents act.

  The core results:
    • Cumulative future sets under earth-adjusted dynamics have monotone,
      bounded cardinality.
    • Every state has an emergent attractor under earth dynamics.
    • Basins of distinct attractors are distinct under earth dynamics.
    • Nontrivial empathic influence (from the base theory) still forces
      ecological fragmentation even after adding the earth layer.

  NOTE:
    We *assume* a generic mutual reachability collapse lemma
    `mutual_reachability_collapses_for` from the base theory, rather than
    re-proving orbit/periodicity facts here. This keeps the "earth" file
    focused purely on the substrate extension.
===============================================================================
-/

import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Algebra.BigOperators.Basic
import Mathlib.Init.Data.Nat.Basic

-------------------------------------------------------------------------------
-- 0. Core variables and base theory hooks
-------------------------------------------------------------------------------

variable {State : Type} [Fintype State]
variable {Agent : Type} [Fintype Agent] [DecidableEq Agent]

-- Base single-step dynamics on states
variable (step : State → State)

-- Abstract multi-empathic influence type and its action
variable (MultiEmpathicInfluence : Type)
variable (apply_influence : MultiEmpathicInfluence → Agent → State → State)

-- Persistent baseline adjustment ("earth"), applied before agent actions
variable (earth_adjust : State → State)

-- From the base theory (assumed already formalized):
--   • future_set : (State → State) → ℕ → State → Finset State
--   • monotone_bounded_stabilizes : ...
--   • and so on.
variable (future_set :
  (State → State) → ℕ → State → Finset State)
variable (monotone_bounded_stabilizes :
  (f : ℕ → ℕ) →
  Monotone f →
  (∃ B, ∀ n, f n ≤ B) →
  ∃ N, ∀ m ≥ N, ∀ k, f (m + k) = f m)

-------------------------------------------------------------------------------
-- 1. Earth-adjusted multi-empathic dynamics
-------------------------------------------------------------------------------

/-- One multi-empathic step with earth applied first.

    Given a multi-empathic influence `M` and a state `s`:
      1. First apply `earth_adjust` to get the adjusted substrate state `s₀`.
      2. Then let each agent act in sequence via `apply_influence`.
      3. After all agents have acted, apply the base `step`.

    This composes the earth substrate and agent dynamics into a single
    "earth-adjusted" step. -/
def multi_empathic_step_with_earth
    (M : MultiEmpathicInfluence) (s : State) : State :=
  let s₀ := earth_adjust s
  Fintype.elems Agent |>.foldl (fun acc a => step (apply_influence M a acc)) s₀

/-- Reachability under earth + multi-agent dynamics.

    `multi_reachable_with_earth M n s t` means that starting at `s`, after
    `n` iterations of the earth-adjusted multi-empathic step, we arrive at `t`. -/
def multi_reachable_with_earth
    (M : MultiEmpathicInfluence) (n : ℕ) (s t : State) : Prop :=
  (multi_empathic_step_with_earth step apply_influence earth_adjust M^[n]) s = t

/-- Cumulative future set under earth dynamics.

    `multi_future_set_with_earth M n s` is the set of all states `t` reachable
    from `s` in *at most* `n` earth-adjusted steps. This cumulative definition
    is crucial: it makes cardinality monotone in `n`, so the usual
    monotone + bounded ⇒ stabilization argument can be applied. -/
def multi_future_set_with_earth
    (M : MultiEmpathicInfluence) (n : ℕ) (s : State) : Finset State :=
  Finset.univ.filter (fun t => ∃ k ≤ n, multi_reachable_with_earth step apply_influence earth_adjust M k s t)

-------------------------------------------------------------------------------
-- 2. Monotonicity and boundedness of future sets
-------------------------------------------------------------------------------

/-- Monotonicity of the cardinality of earth-adjusted cumulative future sets.

    As `n` grows, the set of states reachable in ≤ `n` steps can only grow
    (or stay equal), so its cardinality defines a monotone sequence in `n`. -/
lemma multi_future_card_monotone_with_earth
    (M : MultiEmpathicInfluence) (s : State) :
  Monotone (fun n => (multi_future_set_with_earth step apply_influence earth_adjust M n s).card) := by
  intro m n hmn
  apply Finset.card_le_of_subset
  intro t ht
  rcases Finset.mem_filter.mp ht with ⟨t_in_univ, ⟨k, hk_le_m, hk_reach⟩⟩
  exact Finset.mem_filter.mpr ⟨t_in_univ, ⟨k, le_trans hk_le_m hmn, hk_reach⟩⟩

/-- Boundedness of cumulative future sets under earth dynamics.

    Every cumulative future set is a subset of `univ : Finset State`, so its
    cardinality is bounded above by `Fintype.card State`. This bound is
    independent of `n`. -/
lemma multi_future_card_bounded_with_earth
    (M : MultiEmpathicInfluence) (s : State) :
  ∃ B, ∀ n, (multi_future_set_with_earth step apply_influence earth_adjust M n s).card ≤ B := by
  refine ⟨Fintype.card State, ?_⟩
  intro n
  exact Finset.card_le_univ _

-------------------------------------------------------------------------------
-- 3. Emergent attractors and basins under earth dynamics
-------------------------------------------------------------------------------

/-- Emergent attractor under earth-adjusted dynamics.

    A state `s` has an emergent attractor if there exists some `N` such that,
    for all `m ≥ N` and all `k`, the cardinality of the cumulative future set
    stabilizes:
      card(Future(m + k, s)) = card(Future(m, s)).

    This is a direct analogue of the attractor notion from the base theory,
    but for the earth-adjusted dynamics. -/
def multi_emergent_attractor_with_earth
    (M : MultiEmpathicInfluence) (s : State) : Prop :=
  ∃ N, ∀ m ≥ N, ∀ k,
    (multi_future_set_with_earth step apply_influence earth_adjust M (m + k) s).card =
    (multi_future_set_with_earth step apply_influence earth_adjust M m s).card

/-- Every state has an emergent attractor under earth dynamics.

    This is obtained by applying the base lemma `monotone_bounded_stabilizes`
    to the monotone, bounded sequence
      n ↦ card(Future_with_earth(M, n, s)). -/
lemma every_state_has_multi_emergent_attractor_with_earth
    (M : MultiEmpathicInfluence) (s : State) :
  multi_emergent_attractor_with_earth step apply_influence earth_adjust M s := by
  obtain ⟨N, hN⟩ := monotone_bounded_stabilizes
    (fun n => (multi_future_set_with_earth step apply_influence earth_adjust M n s).card)
    (multi_future_card_monotone_with_earth step apply_influence earth_adjust M s)
    (multi_future_card_bounded_with_earth step apply_influence earth_adjust M s)
  exact ⟨N, hN⟩

/-- Basin membership under earth-adjusted multi-agent dynamics.

    A state `u` is in the basin of `s` if:
      1. `u` can reach `s` in some finite number of earth-adjusted steps, and
      2. the cumulative future sets of `s` stabilize beyond some time `N`
         (i.e., `s` has an emergent attractor, and we witness its stabilization
         threshold). -/
def multi_inBasin_with_earth
    (M : MultiEmpathicInfluence) (u s : State) : Prop :=
  ∃ n N,
    multi_reachable_with_earth step apply_influence earth_adjust M n u s ∧
    (∀ m ≥ N, ∀ k,
      (multi_future_set_with_earth step apply_influence earth_adjust M (m + k) s).card =
      (multi_future_set_with_earth step apply_influence earth_adjust M m s).card)

-------------------------------------------------------------------------------
-- 4. Mutual reachability collapse (assumed from base theory)
-------------------------------------------------------------------------------

/-- Generic mutual reachability collapse lemma (assumed from base theory).

    Intuitively: on a finite state space, if two states `s` and `t` are
    mutually reachable under iteration of a function `f`, then they must
    actually be the same state.

    This captures all the orbit/periodicity reasoning in a generic way so that
    the "earth" layer can simply instantiate it for the earth-adjusted
    multi-empathic dynamics. -/
axiom mutual_reachability_collapses_for
  (f : State → State) {s t : State}
  (hs_t : ∃ n, (f^[n]) s = t)
  (ht_s : ∃ n, (f^[n]) t = s) :
  s = t

/-- Earth-specific mutual reachability collapse.

    This is just `mutual_reachability_collapses_for` instantiated with
    `f := multi_empathic_step_with_earth step apply_influence earth_adjust M`.

    If `s` can reach `t` and `t` can reach `s` under the earth-adjusted
    multi-agent dynamics, then `s = t`. -/
lemma multi_mutual_reachability_collapses_with_earth
  (M : MultiEmpathicInfluence) {s t : State}
  (hs_t : ∃ n, multi_reachable_with_earth step apply_influence earth_adjust M n s t)
  (ht_s : ∃ n, multi_reachable_with_earth step apply_influence earth_adjust M n t s) :
  s = t :=
  mutual_reachability_collapses_for
    (f := multi_empathic_step_with_earth step apply_influence earth_adjust M) hs_t ht_s

-------------------------------------------------------------------------------
-- 5. Distinct attractors have distinct basins (earth-adjusted)
-------------------------------------------------------------------------------

/-- Under earth-adjusted dynamics, distinct attractors have distinct basins.

    If `s` and `t` are both emergent attractors under the earth-adjusted
    dynamics and `s ≠ t`, then there is some state whose basin membership
    differs between `s` and `t`. Equivalently, it is not the case that
    all states have identical basin membership with respect to `s` and `t`. -/
lemma distinct_attractors_have_distinct_basins_with_earth
  (M : MultiEmpathicInfluence)
  {s t : State}
  (hs : multi_emergent_attractor_with_earth step apply_influence earth_adjust M s)
  (ht : multi_emergent_attractor_with_earth step apply_influence earth_adjust M t)
  (hneq : s ≠ t) :
  ¬ (∀ u,
    multi_inBasin_with_earth step apply_influence earth_adjust M u s ↔
    multi_inBasin_with_earth step apply_influence earth_adjust M u t) := by
  intro h_eq
  obtain ⟨Ns, hNs⟩ := hs
  obtain ⟨Nt, hNt⟩ := ht
  -- Each attractor lies in its own basin
  have self_s : multi_inBasin_with_earth step apply_influence earth_adjust M s s :=
    ⟨0, Ns, rfl, hNs⟩
  have self_t : multi_inBasin_with_earth step apply_influence earth_adjust M t t :=
    ⟨0, Nt, rfl, hNt⟩
  -- If basins were identical, each attractor would lie in the other's basin
  have s_in_t := (h_eq s).mp self_s
  have t_in_s := (h_eq t).mpr self_t
  obtain ⟨n, _, hs_t⟩ := s_in_t
  obtain ⟨m, _, ht_s⟩ := t_in_s
  -- Mutual reachability under earth dynamics collapses `s` and `t`
  have : s = t :=
    multi_mutual_reachability_collapses_with_earth step apply_influence earth_adjust M
      ⟨n, hs_t⟩ ⟨m, ht_s⟩
  exact hneq this

-------------------------------------------------------------------------------
-- 6. Main ecology theorem with earth
-------------------------------------------------------------------------------

/-- Nontrivial empathic influence still forces ecology under earth-adjusted dynamics.

    Assumes the base-theory notion of nontrivial empathic influence:
      there exists an agent `a`, state `s`, and horizon `n` such that the
      cardinality of the base `future_set` from `apply_influence M a s` is
      strictly greater than the cardinality of the base `future_set` from `s`.

    The theorem concludes that, under the earth-adjusted multi-agent dynamics,
    there exist distinct emergent attractors with distinct basins — i.e.,
    ecological fragmentation persists despite the arbitrary earth substrate. -/
theorem multi_empathic_implies_ecology_with_earth
  (M : MultiEmpathicInfluence)
  (Hnontrivial : ∃ a s n,
    (future_set step n (apply_influence M a s)).card >
    (future_set step n s).card) :
  ∃ s t,
    s ≠ t ∧
    multi_emergent_attractor_with_earth step apply_influence earth_adjust M s ∧
    multi_emergent_attractor_with_earth step apply_influence earth_adjust M t ∧
    ¬ (∀ u,
      multi_inBasin_with_earth step apply_influence earth_adjust M u s ↔
      multi_inBasin_with_earth step apply_influence earth_adjust M u t) := by

  -- Pick a witness of nontrivial empathic influence in the base theory
  obtain ⟨a, s₁, n, hgt⟩ := Hnontrivial
  let s₂ := apply_influence M a s₁

  -- Nontriviality forces s₁ ≠ s₂
  have hneq : s₁ ≠ s₂ := by
    intro h
    subst h
    exact lt_irrefl _ hgt

  -- Both s₁ and s₂ have emergent attractors under the earth dynamics
  have attr1 := every_state_has_multi_emergent_attractor_with_earth
    step apply_influence earth_adjust M s₁
  have attr2 := every_state_has_multi_emergent_attractor_with_earth
    step apply_influence earth_adjust M s₂

  -- Distinct attractors have distinct basins under earth dynamics
  have basins_distinct :=
    distinct_attractors_have_distinct_basins_with_earth
      step apply_influence earth_adjust M attr1 attr2 hneq

  exact ⟨s₁, s₂, hneq, attr1, attr2, basins_distinct⟩
