/-!
# Emergent Algorithmic Trajectories — Lean Sketch
EmergentAlgorithmicTrajectories.lean

This file formalizes why algorithmic behavior emerges in any
learning-admissible finite medium (ALS), using Unified Computation.

Key points:
1. ALS gives the *potential*: diverging trajectories, recurrent states, bias-sensitivity.
2. Unified Computation provides a universal encoding framework for finite sequences.
3. Combining these, any sufficiently rich periodic trajectory can be interpreted
   as executing an algorithm.
4. This is a *conceptual sketch* — all results are finite and Lean-verifiable,
   except where indicated with `admit` for the UC encoding details.

All comments are intended to guide reasoning, not to add bias or interpretation.
-/

import General-Theory-Of-All-Learning-Systems.AttractorLearningSubstrate
import VulcanLogic.UnifiedComputation

open Classical

namespace VulcanLogic

variables {S : Type} (m : FiniteMedium S)

/-- A trajectory is algorithmic if it can be encoded as a computation
    under the UnifiedComputation framework. -/
def algorithmic_trajectory (x : S) : Prop :=
  ∃ (comp : UnifiedComputation), comp.encodes_trajectory (trajectory m x)

/-- 
Sketch lemma: any periodic trajectory in a nontrivial medium can be encoded
as an algorithmic trajectory.

- `x` is the starting state of a recurrent trajectory with period `k ≥ 1`.
- `h_rich` ensures the medium has at least two distinguishable states, enough
  for a nontrivial encoding.
- The proof is a sketch: the actual construction of `comp` depends on
  the encoding machinery in UnifiedComputation, which guarantees existence.
-/
theorem exists_encoding_for_periodic_trajectory
  (x : S)
  (k : ℕ)
  (hk : k > 0)
  (h_cycle : iterate m k x = x)
  (h_rich : ∃ a b : S, a ≠ b ∧ m.update a ≠ m.update b) :
  ∃ comp : UnifiedComputation, comp.encodes_trajectory (trajectory m x) := by
  -- Step 1: periodic trajectory as infinite sequence
  --   iterate m 0 x, iterate m 1 x, ..., iterate m (k-1) x, repeat infinitely
  -- Step 2: h_rich ensures at least two symbols/states for encoding
  -- Step 3: UnifiedComputation guarantees existence of encoding of any
  --   sufficiently rich periodic sequence as a computation trajectory
  -- Step 4: select comp corresponding to the trajectory of x
  admit -- full construction requires UnifiedComputation encoding implementation

/--
Main theorem: in any learning-admissible finite medium, there exists at least
one algorithmic trajectory.

- Uses ALS to select a recurrent state with period k ≥ 1.
- Applies `exists_encoding_for_periodic_trajectory` to show a comp exists.
- Demonstrates why algorithmic behavior is emergent, not prescribed.
-/
theorem exists_algorithmic_trajectory
  (h_card : Fintype.card S ≥ 2)
  (h_nontrivial : ∃ x y : S, x ≠ y ∧ m.update x ≠ m.update y) :
  ∃ x : S, algorithmic_trajectory m x := by
  -- Step 1: ALS guarantees learning-admissibility
  have adm := learning_admissible m h_card h_nontrivial
  obtain ⟨⟨x_div, y_div, _, h_div⟩, ⟨z, h_rec⟩, _⟩ := adm

  -- Step 2: select recurrent state z
  obtain ⟨k, hk_pos, h_cycle⟩ := h_rec

  -- Step 3: apply sketch lemma to get UnifiedComputation encoding
  have h_enc := exists_encoding_for_periodic_trajectory m z k hk_pos h_cycle h_nontrivial
  obtain ⟨comp, h_comp⟩ := h_enc

  use z
  exact ⟨comp, h_comp⟩

/--
Corollary: algorithmic behavior is inevitable in any nontrivial learning-admissible
finite medium.

- Shows explicitly the Nonempty witness for human-readable interpretation.
-/
corollary algorithmic_emergence
  (h_card : Fintype.card S ≥ 2)
  (h_nontrivial : ∃ x y : S, x ≠ y ∧ m.update x ≠ m.update y) :
  Nonempty (Σ x : S, algorithmic_trajectory m x) :=
  ⟨exists_algorithmic_trajectory m h_card h_nontrivial⟩

end VulcanLogic
