/-!
===============================================================================
Timeline Simulation of Nested Ecologies
Discrete Iterations with Activations and Learning Updates
===============================================================================
-/

import Mathlib
open Finset List

-- 0. Reuse previous finite types
inductive StateSim
| A | B | C
deriving DecidableEq, Fintype

inductive SignalSim
| sig1 | sig2
deriving DecidableEq, Fintype

inductive OperatorSim
| op1
deriving DecidableEq, Fintype

def Trajectory := ℕ → StateSim

-- 1. Step and input
def stepSim (op : OperatorSim) (s : StateSim) (sig : SignalSim) : StateSim :=
  match s, sig with
  | StateSim.A, SignalSim.sig1 => StateSim.B
  | StateSim.B, SignalSim.sig2 => StateSim.C
  | _, _ => s

def inputSim : ℕ → SignalSim :=
  λ t => if t % 2 = 0 then SignalSim.sig1 else SignalSim.sig2

-- 2. Weight function
def weightSim : StateSim → ℝ
| StateSim.A => 1
| StateSim.B => 2
| StateSim.C => 3

-- 3. Decay
def decaySim : ℕ → ℝ := λ t => 1 / (t + 1 : ℝ)

-- 4. Activation
def activationSim (τ : Trajectory) (t : ℕ) : ℝ :=
  decaySim t * weightSim (τ t)

-- 5. Ecology
structure EcologySim where
  name : String
  states : Finset StateSim
  basin  : StateSim → Prop
  weight_update : StateSim → ℝ → StateSim → ℝ
  interacts_with : List (EcologySim × ℕ)

-- 6. Influence & learning
def influences_local_ecologySim (E : EcologySim) (τ : Trajectory) : Prop :=
  ∃ t, τ t ∈ E.states

def induces_learningSim (E : EcologySim) (τ : Trajectory) : Prop :=
  let total_infl := List.sum (List.map (activationSim τ) (List.range 10))
  total_infl > 0 ∧ ∃ s ∈ E.states, E.weight_update s total_infl s ≠ weightSim s

def influential_trajectorySim (E : EcologySim) (τ : Trajectory) : Prop :=
  influences_local_ecologySim E τ ∧ induces_learningSim E τ

-- 7. Multi-spike trajectory
def τ_multi_spikeSim (spikes : List (ℕ × StateSim)) : Trajectory :=
  λ t => match spikes.filter (λ p => p.1 = t) with
        | [] => StateSim.A
        | (_, s)::_ => s

-- 8. Example ecologies
def Ecology1 : EcologySim :=
{ name := "E1",
  states := {StateSim.A, StateSim.B},
  basin := λ s => s = StateSim.A ∨ s = StateSim.B,
  weight_update := λ s infl _ => weightSim s + infl * 0.1,
  interacts_with := [] }

def Ecology2 : EcologySim :=
{ name := "E2",
  states := {StateSim.B, StateSim.C},
  basin := λ s => s = StateSim.B ∨ s = StateSim.C,
  weight_update := λ s infl _ => weightSim s + infl * 0.2,
  interacts_with := [(Ecology1, 2)] }

def ecologiesSim := [Ecology1, Ecology2]

-- 9. Compute activation timeline
def activation_timeline (τ : Trajectory) (t_max : ℕ) : List (ℕ × ℝ) :=
  List.map (λ t => (t, activationSim τ t)) (List.range t_max)

-- 10. Compute influence timeline
def influence_timeline (τ : Trajectory) (ecologies : List EcologySim) (t_max : ℕ) :
  List (ℕ × List String) :=
  List.map (λ t =>
    let active_ecologies := ecologies.filter (λ E => τ t ∈ E.states)
    (t, active_ecologies.map (λ E => E.name)))
    (List.range t_max)

-- 11. Example spike sequence
def spikesSim : List (ℕ × StateSim) := [(0, StateSim.A), (3, StateSim.B), (5, StateSim.C)]
def τSim := τ_multi_spikeSim spikesSim

-- 12. Run simulation
#eval activation_timeline τSim 10
#eval influence_timeline τSim ecologiesSim 10
