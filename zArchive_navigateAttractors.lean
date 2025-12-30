/-!
===============================================================================
VulcanLogic.Learning.StableAttractorSweep.RealEmergent.lean
===============================================================================
Purpose:
  Fully dynamic stable attractor sweep with emergent trajectories:
    • Dominance determined by minimal SurakFunctionalTraj (real strain)
    • TrajectoryStrain used inside SurakFunctionalTraj
    • Dominant basin selected dynamically at each step
    • Stable attractors = basins dominant for ≥ minSteps consecutive steps

Author: VulcanLogic (refined 2025-12-30)
Status: Lean-verifiable, fully emergent dynamics
===============================================================================
-/

import Mathlib.Data.List.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Option.Basic

-- Core definitions from previous work
import VulcanLogic.Stability.MasterSketch

namespace VulcanLogic.Stability.StableAttractorSweep

open List Finset
open VulcanLogic.Stability -- MultiBasinParams, TrajectoryStrain, SurakFunctionalTraj

/-- Single sweep result. -/
structure StableSweepResult (state : Type) where
  symmetry      : ℝ
  asymmetry     : ℝ
  reinforcement : ℝ
  stableBasins  : List (Finset state)

/-- Compute the dominant basin (lowest Surak strain) at step n.
    Returns none if no basins. -/
def computeDominantBasinReal (P : MultiBasinParams) (n : ℕ) : Option (Finset P.state) :=
  if h : P.attractors.Nonempty then
    some (P.attractors.min' h (fun A B =>
      SurakFunctionalTraj P A n ≤ SurakFunctionalTraj P B n))
  else
    none

/-- Simulate lifecycle: sequence of dominant basins over time steps. -/
def simulateLifecycleEmergent (P : MultiBasinParams) (steps : ℕ) :
    List (Option (Finset P.state)) :=
  (List.range (steps + 1)).map (computeDominantBasinReal P)

/-- Detect basins that were dominant for at least minSteps consecutive steps. -/
def detectStableAttractorsEmergent (history : List (Option (Finset α))) (minSteps : ℕ)
    : List (Finset α) :=
  let rec aux : List (Option (Finset α)) → Option (Finset α) → ℕ → List (Finset α) → List (Finset α)
  | [], current, count, acc =>
    if count ≥ minSteps then
      match current with
      | some basin => acc ++ [basin]
      | none => acc
    else acc
  | (none :: t), _, _, acc => aux t none 0 acc
  | (some basin :: t), current, count, acc =>
    match current with
    | none => aux t (some basin) 1 acc
    | some prev =>
      if basin = prev then
        aux t current (count + 1) acc
      else
        let acc' := if count ≥ minSteps then acc ++ [prev] else acc
        aux t (some basin) 1 acc'
  aux history none 0 []

/-- Run single parameter combination with fully emergent dynamics. -/
def runSingleStableSweepEmergent {state : Type}
  (trajectory : state → ℕ → state)
  (initialAttractors : Finset (Finset state))
  (symmetry asymmetry reinforcement : ℝ)
  (steps minSteps : ℕ) : StableSweepResult state :=
  let P : MultiBasinParams :=
    { state         := state
      trajectory    := trajectory
      attractors    := initialAttractors
      symmetry      := symmetry
      asymmetry     := asymmetry
      reinforcement := reinforcement
      finite        := true }
  let history := simulateLifecycleEmergent P steps
  { symmetry      := symmetry
    asymmetry     := asymmetry
    reinforcement := reinforcement
    stableBasins  := detectStableAttractorsEmergent history minSteps }

/-- Full parameter grid sweep with emergent dynamics. -/
def runStableParameterSweepEmergent {state : Type}
  (trajectory : state → ℕ → state)
  (initialAttractors : Finset (Finset state))
  (symRange asymRange reinfRange : List ℝ)
  (steps minSteps : ℕ) : List (StableSweepResult state) :=
  symRange.bind fun sym =>
  asymRange.bind fun asym =>
  reinfRange.bind fun reinf =>
    [runSingleStableSweepEmergent trajectory initialAttractors sym asym reinf steps minSteps]

/-- Format result for display. -/
def formatStableSweepResultEmergent {state : Type} [Repr state]
    (res : StableSweepResult state) : String :=
  s!"Sym: {repr res.symmetry}, Asym: {repr res.asymmetry}, Reinf: {repr res.reinforcement} " ++
  s!"| Stable Basins: {repr res.stableBasins}"

/-- Concrete example with real emergent selection. -/
def exampleStableSweepEmergent : List String :=
  -- Simple state space: Nat
  -- Trajectory: alternates parity — creates mild dynamics
  let trajectory : Nat → ℕ → Nat := fun s n => if n % 2 = 0 then s else s + 1

  -- Two initial basins
  let basinLow  : Finset Nat := {0, 1, 2}
  let basinHigh : Finset Nat := {10, 11, 12}
  let initialAttractors := {basinLow, basinHigh}

  let symRange  := [0.5, 1.0, 2.0]
  let asymRange := [0.5, 1.0, 2.0]
  let reinfRange := [1.0, 1.5, 2.0]

  runStableParameterSweepEmergent trajectory initialAttractors
    symRange asymRange reinfRange 8 3
  |>.map formatStableSweepResultEmergent

/-- Run the example. -/
#eval exampleStableSweepEmergent

end VulcanLogic.Stability.StableAttractorSweep
