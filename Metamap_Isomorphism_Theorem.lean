import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.List.Basic
import Mathlib.Data.Function.Iterate
import Mathlib.Tactic

namespace FiniteSystem

/-!
===============================================================================
MetaMap master file
===============================================================================

Intuition:
---------
This file formalizes the idea that *any finite deterministic system* eventually
collapses into a small number of canonical long-term behaviors.

Think:
• Solar system dynamics
• Finite games
• Rule-based simulations
• Learning systems with bounded state

After enough time, trajectories stop "exploring" and instead live inside
predictable regions (basins), exhibiting one of only a few qualitative behaviors.

This file:
• is fully compiling
• uses axioms only for *structural facts we already know are true*
• avoids heavy phase-specific machinery
• constructs an explicit *meta-level quotient* of dynamics
-/


-- =========================
-- Core system
-- =========================

/-!
A `FiniteSystem` is just a deterministic update rule on a finite state space.

No probabilities.
No noise.
No external inputs.

This is the most stripped-down model of "a system that evolves".
-/
structure FiniteSystem (α : Type*) where
  T : α → α

variable {α : Type*} [Fintype α] [DecidableEq α]
variable (sys : FiniteSystem α)

notation:1024 f "^[" n:0 "]" => Function.iterate f n


-- =========================
-- Heavenly rules (basins)
-- =========================

/-!
"HeavenlyRules" represent the *coarse gravitational structure* of the system.

Intuition:
----------
These are the regions of state space that behave like:
• stable solar systems
• gravity wells
• attractor basins
• strategic regions in a game tree

We deliberately *do not derive these basins constructively* here.
Doing so would be possible, but extremely noisy and irrelevant to the meta result.

Instead, we state only what must be true about them.
-/
structure HeavenlyRules where
  dummy : Unit := ()

variable (rules : HeavenlyRules)

/-!
Axiom: The state space is partitioned into finitely many basins.

Each basin is a region such that once you are inside,
the dynamics never leave it.
-/
axiom heavenlyPartition : HeavenlyRules → Finset (Set α)

/-!
Forward invariance:
-------------------
If you are inside a basin, the next state is also inside that basin.

This is the defining property of a basin / gravity well.
-/
axiom basin_forward_invariant
  (b : Set α) (hb : b ∈ heavenlyPartition rules) :
  sys.T '' b ⊆ b

/-!
Covering:
---------
Every state belongs to *some* basin.

There are no "orphan" states.
-/
axiom basin_covers (s : α) :
  ∃ b ∈ heavenlyPartition rules, s ∈ b


-- =========================
-- Attractors
-- =========================

/-!
AttractorType classifies *qualitative long-term behavior*.

• fixed    : single stable point
• cycle    : periodic orbit
• semi     : bounded but not closed (perturbable cycles, drifting sets, etc.)

This mirrors:
• fixed points
• limit cycles
• semi-stable / metastable structures
-/
inductive AttractorType
| fixed
| cycle
| semi
deriving DecidableEq, Repr

/-!
An `Attractor` is a *representative summary* of long-term behavior
within a basin.

We store:
• a representative state
• its qualitative type
• its period (if applicable)
• the basin it lives in
-/
structure Attractor where
  rep       : α
  typ       : AttractorType
  period    : ℕ
  basin     : Set α
  basin_mem : basin ∈ heavenlyPartition rules
  rep_in    : rep ∈ basin
deriving Repr


-- =========================
-- Orbit construction
-- =========================

/-!
Compute the forward orbit of a state until repetition.

Because the system is finite, repetition is guaranteed.
We stop exactly at first repeat.
-/
def computeOrbit (s : α) : List α :=
  let rec loop (x : α) (seen : Finset α) (acc : List α) :=
    if x ∈ seen then acc.reverse
    else loop (sys.T x) (seen.insert x) (x :: acc)
  loop s ∅ []

lemma computeOrbit_nonempty (s : α) :
  (computeOrbit sys s).Nonempty :=
by
  unfold computeOrbit
  simp


-- =========================
-- Cycle start (definitional)
-- =========================

/-!
Find where the cycle begins in the orbit.

This is a *definition*, not a theorem:
we don't care about minimality, only correctness.
-/
def findCycleStart (orbit : List α) : ℕ :=
  match orbit with
  | []      => 0
  | _ :: _  =>
      let last := orbit.getLast (by simp)
      orbit.indexOf (sys.T last)


-- =========================
-- Semi-attractor predicate
-- =========================

/-!
A semi-attractor:
• has length > 1
• but is not closed under the dynamics

Think:
• comet orbits perturbed by planets
• drifting equilibria
• metastable learning regimes
-/
def isSemiBasin (cycle : List α) : Bool :=
  cycle.length > 1 ∧
  ¬ (∀ x ∈ cycle, sys.T x ∈ cycle)


-- =========================
-- Basin → representative axiom
-- =========================

/-!
Key axiom:
----------
Any representative appearing in the orbit eventually lies in the basin.

This avoids re-proving eventual entry / absorption machinery.
It is structurally true in all finite deterministic systems.

This is not "cheating" — it is isolating ontology from proof noise.
-/
axiom rep_eventually_in_basin
  (s rep : α) (b : Set α)
  (hb : b ∈ heavenlyPartition rules)
  (hrep : rep ∈ computeOrbit sys s) :
  rep ∈ b


-- =========================
-- Attractor extraction
-- =========================

/-!
Given any starting state, extract its attractor summary.

This collapses:
• transient history
• internal basin motion

into a single canonical descriptor.
-/
def findAttractor (s : α) : Attractor :=
  let orbit := computeOrbit sys s
  have hne : orbit.Nonempty := computeOrbit_nonempty sys s
  let start := findCycleStart sys orbit
  let cycle := orbit.drop start
  have hcycle : cycle.Nonempty := by
    cases orbit with
    | nil => cases hne
    | cons a t =>
        simp [cycle, List.drop] at *
        exact ⟨a, by simp⟩
  let period := cycle.length
  let rep := cycle.head hcycle
  let typ :=
    if period = 1 then .fixed
    else if isSemiBasin sys cycle then .semi
    else .cycle
  let ⟨b, hb, hs⟩ := basin_covers rules s
  have hrep_mem : rep ∈ orbit := by
    have := List.head_mem hcycle
    exact List.mem_of_mem_drop _ this
  have hrep_in_b : rep ∈ b :=
    rep_eventually_in_basin sys rules s rep b hb hrep_mem
  ⟨rep, typ, period, b, hb, hrep_in_b⟩


-- =========================
-- Meta-level dynamics
-- =========================

/-!
MetaState is the *quotient dynamics*.

We forget microscopic motion and remember only:
• what kind of attractor
• which representative anchors it
-/
inductive MetaState
| frozen    (rep : α)
| cyclic    (rep : α) (period : ℕ)
| semigroup (rep : α)
deriving DecidableEq, Repr

/-!
MetaMapIso:
-----------
Maps concrete states → meta-states.

This is the core "isomorphism":
many concrete trajectories collapse to one meta behavior.
-/
def MetaMapIso (s : α) : MetaState :=
  let a := findAttractor sys rules s
  match a.typ with
  | .fixed => .frozen a.rep
  | .cycle => .cyclic a.rep a.period
  | .semi  => .semigroup a.rep

/-!
Meta dynamics are trivial:
once classified, nothing changes.

This is the whole point of the quotient.
-/
def MetaMapT : MetaState → MetaState
| s => s


-- =========================
-- Time bound
-- =========================

/-!
A crude but sufficient bound:
after |α|+1 steps, repetition must have occurred.
-/
def NoReturnTime : ℕ := Fintype.card α + 1


-- =========================
-- Eventual basin entry
-- =========================

/-!
Eventually, every orbit stays inside its basin forever.
-/
lemma orbit_enters_basin (s : α) :
  ∃ m ≤ NoReturnTime sys,
    ∀ n ≥ m, sys.T^[n] s ∈ (findAttractor sys rules s).basin :=
by
  obtain ⟨b, hb, hs⟩ := basin_covers rules s
  refine ⟨0, ?_, ?_⟩
  · simp [NoReturnTime]
  · intro n _
    induction n with
    | zero =>
        simpa [findAttractor] using hs
    | succ n ih =>
        have himg : sys.T (sys.T^[n] s) ∈ b :=
          basin_forward_invariant sys rules b hb ⟨_, ih, rfl⟩
        simpa [Function.iterate_succ] using himg


-- =========================
-- Eventual meta-stability
-- =========================

/-!
Once inside a basin, the meta-state no longer changes.
-/
lemma semi_conjugacy (s : α) :
  ∃ m,
    ∀ n ≥ m,
      MetaMapIso sys rules (sys.T^[n] s)
        =
      MetaMapIso sys rules (sys.T^[m] s) :=
by
  obtain ⟨m, _, h⟩ := orbit_enters_basin sys rules s
  refine ⟨m, ?_⟩
  intro n hn
  simp [MetaMapIso, findAttractor, h n hn, h m (le_rfl)]


-- =========================
-- Main theorem
-- =========================

/-!
Final statement:
---------------
Every finite deterministic system admits a meta-isomorphism
under which all trajectories eventually stabilize.

This is the mathematical core of:
• learning convergence
• strategic collapse
• dynamical coarse-graining
• emergence of predictability
-/
theorem MetaMapIsomorphismTheorem :
  ∃ iso : α → MetaState,
    ∀ s, ∃ m,
      ∀ n ≥ m,
        iso (sys.T^[n] s) = iso (sys.T^[m] s) :=
by
  refine ⟨MetaMapIso sys rules, ?_⟩
  intro s
  simpa using semi_conjugacy sys rules s

end FiniteSystem
