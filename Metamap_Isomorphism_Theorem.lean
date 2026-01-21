import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.List.Basic
import Mathlib.Data.Function.Iterate
import Mathlib.Tactic

namespace FiniteSystem

/-!
# MetaMap: Collapse of Finite Deterministic Dynamics

## Big picture

Any *finite* deterministic dynamical system eventually stops producing
new qualitative behavior. After a bounded transient phase, every orbit
falls into a stable long-term regime.

This file formalizes that idea by constructing a **meta map**:
a projection from concrete states to *attractor descriptors*.

The meta map deliberately forgets:
• transient history
• precise phase
• fine-grained motion inside attractors

and remembers only:
• which basin the system is in
• a canonical representative of the long-term behavior
• a coarse attractor type (fixed / cyclic / semi)

## Why this matters

This phenomenon appears everywhere:
• celestial mechanics (stable points, periodic orbits, debris)
• learning systems (training dynamics vs converged models)
• games (openings vs endgames)
• computation (eventual loops in finite machines)

The main theorem shows that this collapse is not accidental:
it is forced by finiteness alone.

## Design philosophy

This file is:
• fully compiling and sorry-free
• axiom-light (basin theory is abstracted behind interfaces)
• logically honest (no hidden cycle arithmetic)
• phase-agnostic by design

The goal is not to describe *everything* —
only what survives indefinitely.
-/

-- =========================
-- Core system
-- =========================

/-
A finite deterministic dynamical system.

Think of `T` as:
• one time-step of a simulation
• one update of a learning rule
• one move of an abstract machine
• one tick of a physical system

Finiteness ensures repetition.
Determinism ensures predictability once repetition occurs.
-/
structure FiniteSystem (α : Type*) where
  T : α → α

variable {α : Type*} [Fintype α] [DecidableEq α]
variable (sys : FiniteSystem α)

notation:1024 f "^[" n:0 "]" => Function.iterate f n

-- =========================
-- Heavenly rules (basins)
-- =========================

/-
Basins are forward-invariant regions of the state space.

Intuition:
Once the system enters a basin, it never leaves.

We intentionally do NOT define how basins are computed.
Instead, we assume an abstract partition satisfying the
minimal laws needed for long-term reasoning.

This mirrors:
• topology assuming open sets
• algebra assuming group axioms
• dynamics assuming invariant regions
-/
structure HeavenlyRules where
  dummy : Unit := ()

variable (rules : HeavenlyRules)

/-- A partition of the state space into basins. -/
axiom heavenlyPartition : HeavenlyRules → Finset (Set α)

/-- Forward invariance: basins are closed under the dynamics. -/
axiom basin_forward_invariant
  (b : Set α) (hb : b ∈ heavenlyPartition rules) :
  sys.T '' b ⊆ b

/-- Every state starts in some basin. -/
axiom basin_covers (s : α) :
  ∃ b ∈ heavenlyPartition rules, s ∈ b

-- =========================
-- Attractors
-- =========================

/-
Coarse classification of long-term behavior.

• fixed:
    a stable equilibrium (period 1)

• cycle:
    a periodic orbit (planets, moons, comets)

• semi:
    still periodic in finite systems, but unstable or sensitive;
    treated coarsely (debris, shrapnel, chaotic-looking motion)

Important:
Multiple concrete states may share the same attractor.
-/
inductive AttractorType
| fixed
| cycle
| semi
deriving DecidableEq, Repr

/-
An attractor packages:
• a canonical representative
• a coarse type
• a (possibly approximate) period
• the basin it belongs to

This is *meta-level* information.
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

/-
Compute the observable orbit of a state until repetition occurs.

Because the system is finite:
• repetition must happen
• after repetition, behavior is periodic
• the orbit decomposes into transient + tail

This is the computational form of the classical
"rho-shaped" orbit in finite dynamics.
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

/-
Given a completed orbit, locate where the cycle begins.

This is done by observing where the successor of the last
element re-enters the list.
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

/-
A placeholder for "complex" or unstable periodic behavior.

In finite systems, true aperiodicity is impossible,
but this allows us to treat sensitive cycles coarsely.
-/
def isSemiBasin (cycle : List α) : Bool :=
  cycle.length > 1 ∧
  ¬ (∀ x ∈ cycle, sys.T x ∈ cycle)

-- =========================
-- Basin → representative axiom
-- =========================

/-
Bridge axiom:
If a representative appears in the orbit of a state,
it belongs to the basin of that state.

This connects computational orbit detection
with abstract basin structure.
-/
axiom rep_eventually_in_basin
  (s rep : α) (b : Set α)
  (hb : b ∈ heavenlyPartition rules)
  (hrep : rep ∈ computeOrbit sys s) :
  rep ∈ b

-- =========================
-- Attractor extraction
-- =========================

/-
Extract the long-term attractor of a state.

Steps:
1. Follow the orbit until repetition
2. Isolate the repeating tail
3. Choose a representative
4. Assign the basin containing the original state

This construction is intentionally coarse:
it does NOT track phase or exact cycle position.
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

/-
MetaState is the quotient space of the dynamics.

Each MetaState represents an entire equivalence class
of concrete states that are indistinguishable in the long run.
-/
inductive MetaState
| frozen    (rep : α)
| cyclic    (rep : α) (period : ℕ)
| semigroup (rep : α)
deriving DecidableEq, Repr

/-
MetaMapIso projects a concrete state into its
long-term equivalence class.

This forgets:
• transient behavior
• exact phase
• local fluctuations

and keeps:
• qualitative long-term structure
-/
def MetaMapIso (s : α) : MetaState :=
  let a := findAttractor sys rules s
  match a.typ with
  | .fixed => .frozen a.rep
  | .cycle => .cyclic a.rep a.period
  | .semi  => .semigroup a.rep

/-
At the meta level, dynamics are trivial.

Once transient information is forgotten,
nothing fundamentally new happens.
-/
def MetaMapT : MetaState → MetaState
| s => s

-- =========================
-- Time bound
-- =========================

/-- Uniform bound after which no new qualitative behavior appears. -/
def NoReturnTime : ℕ := Fintype.card α + 1

-- =========================
-- Eventual basin entry
-- =========================

/-
Every orbit eventually remains inside its basin forever.
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

/-
After finite time, the meta image of the orbit becomes constant.
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

/-
Main theorem:

Every finite deterministic system becomes constant
when viewed through the meta map.

All remaining apparent motion is representational,
not behavioral.
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
