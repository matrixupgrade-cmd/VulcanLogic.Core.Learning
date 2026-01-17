/-!
===============================================================================
PathOfLoki.lean
Unified Constructive Trickster Model
===============================================================================

Author: Sean Timothy
Date: 2026-01-17

Purpose:
  • Confidence preorder → observer lag
  • Rule neutrality → zones where Loki "disappears"
  • Neutral paths → infinite exploitation of observer paralysis
  • Basin-indexed & multi-observer extension
  • Multi-step itinerary / steering
===============================================================================
-/

namespace PathOfLoki

/-- Abstract types -/
variable (State Basin Observer : Type)
variable (basin_of : State → Basin)

/-- Confidence is a preorder over states for each observer -/
class ConfidencePreorder (State : Type) (Observer : Type) :=
  (conf : Observer → State → State → Prop)
  (refl : ∀ o s, conf o s s)
  (trans : ∀ o s₁ s₂ s₃, conf o s₁ s₂ → conf o s₂ s₃ → conf o s₁ s₃)

variable [ConfidencePreorder State Observer]
notation s₁ " ⪯[" o "] " s₂ => ConfidencePreorder.conf o s₁ s₂

/-!
------------------------------------------------------------------------------
Loki Steps and Paths
------------------------------------------------------------------------------
-/

/-- A step reduces or maintains confidence for a given observer -/
def LokiStep (o : Observer) (s₁ s₂ : State) : Prop :=
  ¬ (s₁ ⪯[o] s₂)

/-- Loki path: each step avoids increasing observer confidence -/
def LokiPath (o : Observer) (path : Nat → State) : Prop :=
  ∀ n, LokiStep o (path n) (path (n+1))

/-- Observer catch-up: eventually regains confidence -/
def CatchUpTime (o : Observer) (path : Nat → State) : Prop :=
  ∃ k, ∀ n ≥ k, path n ⪯[o] path (n+1)

/-- Loki advantage: infinitely many steps where confidence does not increase -/
def LokiAdvantage (o : Observer) (path : Nat → State) : Prop :=
  ∀ k, ∃ n ≥ k, ¬ (path n ⪯[o] path (n+1))

/-- Theorem: Loki path → no finite catch-up -/
theorem no_catch_up_of_loki_path
  (o : Observer) (path : Nat → State) (hLoki : LokiPath o path) :
  ¬ CatchUpTime o path := by
  intro hCatch
  rcases hCatch with ⟨k, hk⟩
  have := hLoki k
  have hk' := hk k (le_rfl)
  exact this hk'

/-!
------------------------------------------------------------------------------
Rule Neutrality
------------------------------------------------------------------------------
-/

/-- Total neutrality: no gradient in confidence exists to any next state -/
def RuleNeutrality (o : Observer) (s : State) : Prop :=
  ∀ s', ¬ (s ⪯[o] s') ∧ ¬ (s' ⪯[o] s)

/-- Weak neutrality: no strictly better next state (allows equality or incomparability) -/
def StrictConfIncrease (o : Observer) (s s' : State) : Prop :=
  s ⪯[o] s' ∧ ¬ (s' ⪯[o] s)

def WeakRuleNeutrality (o : Observer) (s : State) : Prop :=
  ∀ s', ¬ StrictConfIncrease o s s'

/-- Basin-indexed neutrality (optional) -/
def BasinNeutrality (o : Observer) (b : Basin) (s : State) : Prop :=
  basin_of s = b ∧ RuleNeutrality o s

/-- Multi-observer neutrality (arms races, multiple observers) -/
def MultiNeutral (os : Set Observer) (s : State) : Prop :=
  ∀ o ∈ os, RuleNeutrality o s

/-- Neutral Loki Path: visits rule-neutral states infinitely often -/
def NeutralLokiPath (o : Observer) (path : Nat → State) : Prop :=
  LokiPath o path ∧ ∀ k, ∃ n ≥ k, RuleNeutrality o (path n)

/-- Lemma: RuleNeutrality blocks increases -/
lemma neutrality_blocks_increase (o : Observer) (s s' : State)
  (hNeut : RuleNeutrality o s) : ¬ (s ⪯[o] s') :=
hNeut s' |>.1

/-- Theorem: Neutral paths → Loki advantage -/
theorem neutral_loki_implies_advantage
  (o : Observer) (path : Nat → State) (hNeutral : NeutralLokiPath o path) :
  LokiAdvantage o path := by
  intro k
  rcases hNeutral.2 k with ⟨n, hn_ge, hn_neut⟩
  have h_no_inc : ¬ (path n ⪯[o] path (n+1)) :=
    neutrality_blocks_increase o (path n) (path (n+1)) hn_neut
  exact ⟨n, hn_ge, h_no_inc⟩

/-!
------------------------------------------------------------------------------
Multi-Basin Loki Itinerary
------------------------------------------------------------------------------
-/

/-- Abstract steering action: move within basin while preserving neutrality -/
def LokiSteerBasin (os : Set Observer) (b : Basin) (s : State) : State := s
-- Placeholder: could be moving pieces, symmetry shifts, etc.

/-- Loki itinerary: infinite path across basins in priority order, maintaining multi-observer neutrality -/
def LokiItinerary (os : Set Observer) (bs : Set Basin) (path : Nat → State) : Prop :=
  ∀ n,
    let candidates := bs in
    ∃ b ∈ candidates,
      path (n+1) = LokiSteerBasin os b (path n) ∧
      MultiNeutral os (path (n+1))

/-- Theorem (sketch): Multi-step itinerary preserves advantage for all observers -/
theorem LokiItineraryMaintainsAdvantage
  (os : Set Observer)
  (bs : Set Basin)
  (path : Nat → State)
  (hItin : LokiItinerary os bs path) :
  ∀ o ∈ os, LokiAdvantage o path := by
  intro o ho k
  -- Induction on k to find a later neutral step
  induction k using Nat.strongInductionOn with
  | ind k ih =>
    -- From itinerary, every step lands in multi-neutral
    -- ∴ infinitely many neutrals after k
    have h_next : ∃ n ≥ k, MultiNeutral os (path n) := by
      use k  -- Base at k, but actually iterate forward
      -- Here assume path starts neutral or steers to one; in full proof, use hItin to show recurrence
      admit
    rcases h_next with ⟨n, hn_ge, hn_multi⟩
    -- MultiNeutral implies RuleNeutrality for this o
    have hn_neut : RuleNeutrality o (path n) := hn_multi o ho
    -- Neutrality blocks increase to next
    have h_no_inc : ¬ (path n ⪯[o] path (n+1)) :=
      neutrality_blocks_increase o (path n) (path (n+1)) hn_neut
    exact ⟨n, hn_ge, h_no_inc⟩

/-!
-- Suggestions for extensions:
-- 1. Strengthen LokiSteerBasin: make it return a state that preserves MultiNeutral and optionally approaches EoC.
--    e.g., axiom steer_preserves_neutral : ∀ os b s, MultiNeutral os (LokiSteerBasin os b s)
-- 2. Add strict decrease for "prank reveals": def StrictLokiStep o s1 s2 := StrictConfIncrease o s2 s1 (reverse gradient).
-- 3. Concrete toy: Define State = Fin 5 (small graph), basins as subsets, explicit preorder table, compute an itinerary path.
-- 4. Observer adaptation: Allow observers to evolve their preorder over time, e.g., via a meta-function on paths.
-- 5. Integrate EoC: Def EdgeOfCriticality (b : Basin) : Prop, then steer toward basins where EoC holds without losing neutrality.
-/

end PathOfLoki

/-!
------------------------------------------------------------------------------
Edge-of-Criticality Advisory (Conceptual, Non-Operational)
------------------------------------------------------------------------------

Purpose:
  • Provide a conceptual hook for trickster strategies that exploit system
    instability without committing to specific metrics.
  • Maintain maximal generality: no axioms, no numeric entropy, no functional
    EoC calculation is required.
  • Capture the idea of "pushing a basin toward chaos" to hide actions,
    stall observers, or manipulate competing basins.

Core Idea:
  Loki observes basins and their dynamics.
  Instead of calculating exact critical points, Loki may:
    • Increase apparent complexity (tension, randomness) to stall
      observer rule application.
    • Reduce tension to blend into background, avoiding detection.
    • Switch symmetry axes to make rules ineffective, creating "blind spots."
  This is entirely conceptual: the file does not implement or assume
  an EoC function.

Interpretive Examples:
  • Poker: forcing an opponent into lines too complex to compute optimally.
  • Risk: creating border tensions that stall invasion heuristics.
  • Biology: predator flaps wing to make prey rules ineffective (stalling escape
    or camouflage responses).
  • Ecology: nudging competing agents to a local instability so their rules
    become non-informative.

Suggested Extension Points (Optional for Future Formalization):
  • Define `EdgeOfCriticality : Basin → Prop` to mark high-tension zones.
  • Extend `LokiSteerBasin` to optionally select moves that approach EoC
    without leaving the neutral corridor.
  • Relate EoC approach to confidence preorders: no step should allow an
    observer confidence increase beyond current maxima.

Invariant Captured Conceptually:
  "Even when basins are near instability, Loki remains hidden or uncatchable
   to observer models by leveraging rule-neutral corridors."
------------------------------------------------------------------------------
-/
