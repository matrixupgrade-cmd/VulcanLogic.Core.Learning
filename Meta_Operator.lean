import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.Prime

/-
  meta_operator.lean

  External meta-operators that cultivate opaque dynamical basins via
  finite histories of asymmetry fingerprints.

  The meta-operator has **no access** to the true update rule and only limited
  measurements (fingerprints from history). It detects high-stress zones
  (bounded drift violations or rare events), diagnoses fragility, and
  conservatively adapts policy to preserve and grow basin viability.

  No omniscience. No optimization objective. No convergence assumption.
  Goal: avoid collapse signatures and stabilize positive viability drift.
-/

namespace MetaOperator

-- ────────────────────────────────────────────────────────────────
-- 0. Assumed primitives
-- ────────────────────────────────────────────────────────────────

variable {Board : Type*}                 -- finite dynamical substrate
variable {AsymmetryFingerprint : Type*}  -- stress signature (affected, tilt, drift scalar)

variable (board_fingerprint : Board → AsymmetryFingerprint)

variable (bounded_drift     : AsymmetryFingerprint → Prop)
variable (rare_event        : AsymmetryFingerprint → Prop)
variable (edge_of_criticality : Board → Prop)

-- Abstract viability scalar — what the basin "wants" to preserve/grow
variable (viability : AsymmetryFingerprint → ℝ)

-- ────────────────────────────────────────────────────────────────
-- 1. Observation & history
-- ────────────────────────────────────────────────────────────────

structure Observation where
  time        : ℕ
  fingerprint : AsymmetryFingerprint

abbrev History := List Observation

-- Utility: get last fingerprint safely
def last_fingerprint (h : History) : Option AsymmetryFingerprint :=
  h.getLast?.map Observation.fingerprint

-- ────────────────────────────────────────────────────────────────
-- 2. Interventions & meta-operator
-- ────────────────────────────────────────────────────────────────

variable {Intervention : Type*}
variable (admissible : Intervention → Prop)

structure MetaOperator where
  policy : History → Intervention

def sound (meta : MetaOperator) : Prop :=
  ∀ h, admissible (meta.policy h)

-- ────────────────────────────────────────────────────────────────
-- 3. External shaping
-- ────────────────────────────────────────────────────────────────

variable (base_update       : Board → Board)
variable (apply_intervention : Intervention → (Board → Board) → (Board → Board))

def effective_update (meta : MetaOperator) (h : History) : Board → Board :=
  apply_intervention (meta.policy h) base_update

lemma effective_update_admissible
  (meta : MetaOperator) (h : History) (hsound : sound admissible meta) :
  admissible (meta.policy h) :=
hsound h

-- ────────────────────────────────────────────────────────────────
-- 4. Stress, rarity, acceptance linkage
-- ────────────────────────────────────────────────────────────────

axiom rare_event_breaks_bounded_drift ⦃fp : AsymmetryFingerprint⦄
  (hrare : rare_event fp) : ¬ bounded_drift fp

def fingerprint_after_n (upd : Board → Board) (n : ℕ) (b₀ : Board) : AsymmetryFingerprint :=
  board_fingerprint (Nat.iterate upd n b₀)

def simple_acceptance (b₀ : Board) (upd : Board → Board) : Prop :=
  ∀ n ≥ 1, bounded_drift (fingerprint_after_n upd n b₀)

lemma acceptance_implies_bounded_drift
  (meta  : MetaOperator)
  (board : Board)
  (h     : History)
  (hnonempty : h.Nonempty)
  (hacc  : simple_acceptance board (effective_update meta h)) :
  bounded_drift ((h.getLast?.map Observation.fingerprint).getD default) :=
by
  obtain ⟨obs, tail, rfl⟩ := hnonempty
  have : (h.getLast?.map Observation.fingerprint).getD default = obs.fingerprint := by
    simp [List.getLast?_cons_cons, *]
  rw [this]
  have : obs.time ≥ 1 := by simp [Observation.time]
  exact hacc obs.time this

lemma rare_event_breaks_acceptance
  (meta  : MetaOperator)
  (board : Board)
  (h     : History)
  (hnonempty : h.Nonempty)
  (hrare : rare_event ((h.getLast?.map Observation.fingerprint).getD default))
  (hacc  : simple_acceptance board (effective_update meta h)) :
  False :=
by
  have := acceptance_implies_bounded_drift meta board h hnonempty hacc
  exact rare_event_breaks_bounded_drift hrare this

-- ────────────────────────────────────────────────────────────────
-- 5. Basin & harmony-growth goal
-- ────────────────────────────────────────────────────────────────

structure Basin where
  carrier : Board

variable (harmonious     : Basin → AsymmetryFingerprint → Prop)
variable (growth_positive : Basin → AsymmetryFingerprint → Prop)

-- Strict harmony includes bounded drift guarantee
def harmonious_strict (basin : Basin) (fp : AsymmetryFingerprint) : Prop :=
  harmonious basin fp ∧ bounded_drift fp

def harmony_growth_meta
  (meta  : MetaOperator)
  (basin : Basin) : Prop :=
∃ horizon : ℕ,
  ∀ h : History, h.length ≥ horizon → h.Nonempty →
    let last_fp := (h.getLast?.map Observation.fingerprint).getD default
    harmonious_strict basin last_fp ∧ growth_positive basin last_fp

lemma harmony_growth_nonempty
  (meta  : MetaOperator)
  (basin : Basin)
  (hharmony : harmony_growth_meta meta basin)
  {horizon : ℕ} :
  ∀ h, h.length ≥ horizon → h.Nonempty :=
by
  obtain ⟨horizon', h_hor⟩ := hharmony
  intro h hh
  exact (h_hor h hh).1.1.nonempty

lemma harmonious_strict_implies_bounded_drift
  (basin : Basin) (fp : AsymmetryFingerprint)
  (h_strict : harmonious_strict basin fp) :
  bounded_drift fp :=
h_strict.2

-- ────────────────────────────────────────────────────────────────
-- 6. Operational semantics
-- ────────────────────────────────────────────────────────────────

inductive StepResult
  | continue (next_board : Board) (obs : Observation) (next_history : History)
  | stable

def run_step (meta : MetaOperator) (b : Board) (history : History) : StepResult :=
  let intervention := meta.policy history
  let next_board := effective_update meta history b
  let fp := board_fingerprint next_board
  let obs := { time := history.length + 1, fingerprint := fp }
  StepResult.continue next_board obs (history ++ [obs])

def generate_history_aux (meta : MetaOperator) (b : Board) (fuel : ℕ) (history : History) : History :=
  match fuel with
  | 0     => history
  | fuel+1 =>
    match run_step meta b history with
    | StepResult.continue _ _ next_h => generate_history_aux meta next_h fuel
    | StepResult.stable               => history

def generate_history (meta : MetaOperator) (b₀ : Board) (steps : ℕ) : History :=
  generate_history_aux meta b₀ steps []

lemma generate_history_length_le
  (meta : MetaOperator) (b₀ : Board) (steps : ℕ) :
  (generate_history meta b₀ steps).length ≤ steps :=
by
  induction steps generalizing b₀ with
  | zero => simp [generate_history, generate_history_aux]
  | succ n ih =>
    simp [generate_history, generate_history_aux]
    cases run_step meta b₀ (generate_history meta b₀ n) <;> simp [ih]

-- ────────────────────────────────────────────────────────────────
-- 7. Stress diagnosis & policy adaptation
-- ────────────────────────────────────────────────────────────────

def high_stress_zone (fp : AsymmetryFingerprint) : Prop :=
  ¬ bounded_drift fp ∨ rare_event fp

def fingerprint_diagnostic (fp : AsymmetryFingerprint) : String :=
  if high_stress_zone fp then "HIGH STRESS: drift violation or rare event"
  else if viability fp < 0 then "NEGATIVE VIABILITY: shrinking"
  else "STABLE: policy viable"

-- Conservative fallback on recent stress detection
def avoid_recent_stress_policy (fallback : Intervention) (meta : MetaOperator) (h : History) : Intervention :=
  match h.reverse with
  | [] => meta.policy []
  | obs :: _ =>
      if high_stress_zone obs.fingerprint then fallback else meta.policy h

lemma stress_triggers_fallback
  (fallback : Intervention)
  (meta : MetaOperator)
  (h : History)
  (hnonempty : h.Nonempty)
  (hstress : high_stress_zone ((h.getLast?.map Observation.fingerprint).getD default)) :
  avoid_recent_stress_policy fallback meta h = fallback :=
by
  obtain ⟨obs, tail, rfl⟩ := hnonempty
  simp [avoid_recent_stress_policy, hstress]

-- ────────────────────────────────────────────────────────────────
-- 8. Preservation theorems
-- ────────────────────────────────────────────────────────────────

def recent_n_fingerprints (h : History) (n : ℕ) : List AsymmetryFingerprint :=
  h.takeRight n |>.map Observation.fingerprint

def edge_of_criticality_windowed (h : History) (window : ℕ) : Prop :=
  ∀ fp ∈ recent_n_fingerprints h window, bounded_drift fp

theorem harmony_growth_preserves_windowed_eoc
  (meta  : MetaOperator)
  (basin : Basin)
  (hsound   : sound admissible meta)
  (hharmony : harmony_growth_meta meta basin)
  (window : ℕ) (hwindow : window > 0) :
  edge_of_criticality_windowed
    (generate_history meta basin.carrier window) window :=
by
  let h := generate_history meta basin.carrier window
  have h_len_le : h.length ≤ window := generate_history_length_le meta basin.carrier window
  have h_nonempty : h.Nonempty := harmony_growth_nonempty meta basin hharmony h_len_le
  intro fp h_mem
  simp [recent_n_fingerprints, List.mem_map] at h_mem
  obtain ⟨obs, h_obs, rfl⟩ := h_mem
  obtain ⟨horizon, h_hor⟩ := hharmony
  have h_safe : harmonious_strict basin obs.fingerprint :=
    (h_hor h (by linarith [h_len_le]) h_nonempty).1
  exact harmonious_strict_implies_bounded_drift basin obs.fingerprint h_safe

-- ────────────────────────────────────────────────────────────────
-- 9. Meta-operator as bounded cultivator (general viability loop)
-- ────────────────────────────────────────────────────────────────

def cultivate_step (meta : MetaOperator) (basin : Basin) (history : History) : MetaOperator × History :=
  let fallback := some "safer intervention"  -- placeholder conservative action
  let next_h := generate_history meta basin.carrier 1 ++ history
  let last_fp := (next_h.getLast?.map Observation.fingerprint).getD default
  let diagnostic := fingerprint_diagnostic last_fp
  let updated_policy := avoid_recent_stress_policy fallback meta
  ({ policy := updated_policy }, next_h)

def cultivate_iterate
  (meta : MetaOperator) (basin : Basin) (history : History) (fuel : ℕ) :
  MetaOperator × History :=
Nat.iterate (λ p => cultivate_step p.1 basin p.2) fuel (meta, history)

theorem meta_operator_eventually_stabilizes_viability
  (meta₀ : MetaOperator)
  (basin : Basin)
  (hharmony : harmony_growth_meta meta₀ basin)
  (max_iters : ℕ)
  (drift_pos : ∀ fp, bounded_drift fp → viability fp ≥ 0) :
  ∃ horizon ≤ max_iters,
    ∀ steps ≥ horizon,
      let (meta', h') := cultivate_iterate meta₀ basin [] steps
      let last_fp := (h'.getLast?.map Observation.fingerprint).getD default
      bounded_drift last_fp ∧ viability last_fp ≥ 0 :=
by
  obtain ⟨horizon, h_hor⟩ := hharmony
  use horizon, Nat.min_le_right _ _
  intro steps hsteps
  let (meta', h') := cultivate_iterate meta₀ basin [] steps
  let last_fp := (h'.getLast?.map Observation.fingerprint).getD default
  have h_safe : harmonious_strict basin last_fp :=
    h_hor h' (by linarith [h'.length]) (by
      cases h'.reverse with
      | nil => exact absurd rfl (by decide)
      | cons _ _ => exact ⟨_, _, rfl⟩)
  have h_drift : bounded_drift last_fp := harmonious_strict_implies_bounded_drift _ _ h_safe
  have h_viable : viability last_fp ≥ 0 := drift_pos _ h_drift
  exact ⟨h_drift, h_viable⟩

end MetaOperator
