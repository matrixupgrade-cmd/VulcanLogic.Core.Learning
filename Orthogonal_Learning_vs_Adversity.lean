/-!
# Orthogonal_Learning_vs_Adversity

Formalization of orthogonal agent-basin dynamics and
combinatorial resilience against predatory basins.

High optionality + branching ensures the orthogonal group
has unreachable monotone branches that a single predator
cannot cover within a bounded horizon.
-/

import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Algebra.BigOperators.Basic

universe u

variable {α : Type u} [Fintype α]

/-! ## Core Types -/

structure Agent where
  act : α → α

structure Basin where
  traj : α → ℕ → α   -- deterministic time-indexed evolution

/-! ## Composition and Trajectories -/

infixr:60 " ⊙ " => fun (a : Agent) (b : Basin) =>
  fun s => b.traj (a.act s) 0

def agentTraj (a : Agent) (b : Basin) (s₀ : α) : ℕ → α
  | 0     => s₀
  | n + 1 => (a ⊙ b) (agentTraj a b s₀ n)

/-! ## Witness and Orthogonality -/

def MonotoneAlongTraj (traj : ℕ → α) (W : α → ℕ) : Prop :=
  ∀ n, W (traj (n + 1)) ≥ W (traj n)

def Orthogonal (W : α → ℕ) (a : Agent) (b : Basin) (s₀ : α) : Prop :=
  MonotoneAlongTraj (agentTraj a b s₀) W

lemma orthogonal_preserves (W : α → ℕ) (a : Agent) (b : Basin) (s₀ : α)
    (h : Orthogonal W a b s₀) :
    ∀ n, W (agentTraj a b s₀ n) ≥ W s₀ := by
  intro n
  induction n with
  | zero => rfl
  | succ n ih => exact ih.trans (h n)

/-! ## Group Structures -/

def OrthogonalToGroup (W : α → ℕ) (a : Agent) (group : Finset Basin) (s₀ : α) : Prop :=
  ∀ b ∈ group, Orthogonal W a b s₀

def perturbStates (a : Agent) (b : Basin) (s₀ : α) (δ : ℕ) : Finset α :=
  (Finset.range (δ + 1)).image (fun k => agentTraj a b s₀ k)

def reachableUnderGroupPerturb (a : Agent) (group : Finset Basin) (s₀ : α) (δ : ℕ) : ℕ :=
  (group.biUnion (fun b => perturbStates a b s₀ δ)).card

def HighOptionality (a : Agent) (group : Finset Basin) (s₀ : α) (δ min_branch : ℕ) : Prop :=
  reachableUnderGroupPerturb a group s₀ δ ≥ group.card * min_branch

/-! ## Predator and Robustness -/

def predatorVisible (a : Agent) (b_pred : Basin) (s₀ : α) (δ : ℕ) : Finset α :=
  (Finset.range (δ + 1)).image (fun k => agentTraj a b_pred s₀ k)

def Destructive (W : α → ℕ) (a : Agent) (b_pred : Basin) (s₀ : α) : Prop :=
  ∃ n, W (agentTraj a b_pred s₀ (n + 1)) < W (agentTraj a b_pred s₀ n)

/-! ## Cardinality Helpers -/

lemma perturbStates_card_le (a : Agent) (b : Basin) (s₀ : α) (δ : ℕ) :
    (perturbStates a b s₀ δ).card ≤ δ + 1 :=
  Finset.card_image_le.trans (Finset.card_range (δ + 1))

lemma predatorVisible_card_le (a : Agent) (b_pred : Basin) (s₀ : α) (δ : ℕ) :
    (predatorVisible a b_pred s₀ δ).card ≤ δ + 1 :=
  Finset.card_image_le.trans (Finset.card_range (δ + 1))

/-! ## Main Theorem: Combinatorial Evasion -/

lemma orthogonal_group_has_unreachable_monotone_branch
    (W : α → ℕ) (a : Agent) (group : Finset Basin) (b_pred : Basin)
    (s₀ : α) (δ min_branch : ℕ)
    (h_ortho : OrthogonalToGroup W a group s₀)
    (h_opt : HighOptionality a group s₀ δ min_branch)
    (h_critical : group.card * min_branch > δ + 1) :
    ∃ b ∈ group, ∃ k ≤ δ,
      W (agentTraj a b s₀ k) ≥ W s₀ ∧
      agentTraj a b s₀ k ∉ predatorVisible a b_pred s₀ δ := by
  -- Predator can see at most δ+1 states in its horizon
  have h_pred_card : (predatorVisible a b_pred s₀ δ).card ≤ δ + 1 :=
    predatorVisible_card_le a b_pred s₀ δ

  -- Group produces at least group.card * min_branch distinct reachable states
  have h_group_branches : reachableUnderGroupPerturb a group s₀ δ ≥ group.card * min_branch :=
    h_opt

  -- Criticality: group branching exceeds predator horizon
  have h_gt : reachableUnderGroupPerturb a group s₀ δ > δ + 1 := by
    apply Nat.lt_of_le_of_lt _ h_group_branches
    exact Nat.lt_of_succ_le h_critical

  -- By pigeonhole: not every group branch state can lie on the predator's trajectory
  by_contra h_all_covered
  push_neg at h_all_covered

  -- If every reachable group state is visible to predator → total branches ≤ predator visible
  have h_covered_card : reachableUnderGroupPerturb a group s₀ δ ≤ δ + 1 := by
    apply Finset.card_le_of_subset
    intro x hx
    simp only [reachableUnderGroupPerturb, Finset.mem_biUnion] at hx
    rcases hx with ⟨b, hb, hx_in, rfl⟩
    exact h_all_covered b hb x hx_in

  linarith

/-!
Design Notes:
• Under sufficient group size and per-basin branching (criticality condition),
  the orthogonal group necessarily possesses at least one monotone (safe)
  state reachable within δ steps that lies outside the predator's δ-horizon.
• This is pure combinatorial evasion: the predator cannot cover all viable branches.
• The proof uses only pigeonhole on finite sets; no probabilities or extra structure.
-/
