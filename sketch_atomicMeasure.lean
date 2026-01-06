import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Basic
import Mathlib.Data.Fin.Basic

variable {State Action : Type*}

-- Finite set of atomic measure kinds available to agents
inductive AtomicMeasureKind
  | localValue
  | anticipationWeight
  | distanceToRef
  | persistenceScore
  | coverage
  | risk
  deriving Repr, DecidableEq

instance : Fintype AtomicMeasureKind :=
  ⟨{AtomicMeasureKind.localValue, AtomicMeasureKind.anticipationWeight,
    AtomicMeasureKind.distanceToRef, AtomicMeasureKind.persistenceScore,
    AtomicMeasureKind.coverage, AtomicMeasureKind.risk}, by simp⟩

/-- Atomic evaluation functions — one per kind, possibly parameterized -/
variable (atomic_eval : AtomicMeasureKind → State → ℝ)

/-- Composite evaluative measure as weighted sum over atomic kinds -/
def composite_eval (weights : AtomicMeasureKind → ℝ) (s : State) : ℝ :=
  ∑ k : AtomicMeasureKind, weights k * atomic_eval k s

/-- Abstract agent policy and step -/
variable (step : State → Action → State)
variable (policy : State → Action)

/-- Monotone policy w.r.t a given weighting of atomic measures -/
def MonotoneWithWeights (weights : AtomicMeasureKind → ℝ) : Prop :=
  ∀ s : State,
    composite_eval atomic_eval weights (step s (policy s))
      ≥ composite_eval atomic_eval weights s
