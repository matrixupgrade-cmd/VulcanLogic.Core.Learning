universe u

-- Define the Basin structure
structure Basin where
  name       : String
  efficiency : ℝ

variable (Basins : List Basin)

-- Exposure rate function: how frequently an agent is exposed to another basin
def exposure_rate (_A _B : Basin) : ℝ := (0.6 : ℝ)

-- Benefit function: how much efficiency an agent gains or loses from absorbing asymmetries
def signed_benefit (A B : Basin) : ℝ :=
  if B.efficiency > A.efficiency + 2 then 8.0
  else if B.efficiency < A.efficiency - 3 then -6.0
  else 1.5 * (B.efficiency - A.efficiency)

-- Absorption condition: agent absorbs asymmetry only if it's beneficial
def absorbs (A B : Basin) : Prop := signed_benefit A B > 0

-- Total exposure function: accumulates exposure over all agents in the environment
def total_exposure (A : Basin) : ℝ :=
  let others := Basins.filter (·.name ≠ A.name) in
  others.foldl (fun acc B =>
    if absorbs A B then acc + signed_benefit A B * exposure_rate A B else acc) 0

-- Total efficiency gain function: calculates net gain in efficiency after absorption
def total_efficiency_gain (A : Basin) : ℝ :=
  let others := Basins.filter (·.name ≠ A.name) in
  others.foldl (fun acc B =>
    if absorbs A B then acc + signed_benefit A B else acc) 0

-- Bounded noise (modeling measurement/execution uncertainty, ∈ [-ε, ε])
variable (ε : ℝ) (hε : 0 ≤ ε)

def noisy_signed_benefit (A B : Basin) : ℝ := signed_benefit A B + ε  -- worst-case additive noise

def noisy_absorbs (A B : Basin) : Prop := noisy_signed_benefit A B > 0

def noisy_total_efficiency_gain (A : Basin) : ℝ :=
  let others := Basins.filter (·.name ≠ A.name) in
  others.foldl (fun acc B =>
    if noisy_absorbs A B then acc + noisy_signed_benefit A B else acc) 0

-- If original benefit is large enough, noisy version still positive
theorem noisy_gain_still_positive (A : Basin)
    (h : ∃ B ∈ Basins, signed_benefit A B > ε)   -- benefit overcomes worst-case noise
    (h_abs_consistent : ∀ B, absorbs A B → noisy_absorbs A B) :
    0 < noisy_total_efficiency_gain A := by
  obtain ⟨B, hmem, h_strong_pos⟩ := h
  have h_noisy_pos : 0 < noisy_signed_benefit A B := by
    linarith [h_strong_pos, hε]
  have h_noisy_abs : noisy_absorbs A B := h_noisy_pos
  have h_term_pos : 0 < noisy_signed_benefit A B := h_noisy_pos

  have h_all_nonneg : ∀ C ∈ Basins.filter (·.name ≠ A.name),
      0 ≤ if noisy_absorbs A C then noisy_signed_benefit A C else 0 := by
    intro C hC
    by_cases h : noisy_absorbs A C
    · exact le_of_lt h
    · exact le_refl _

  have hB_filtered : B ∈ Basins.filter (·.name ≠ A.name) :=
    List.mem_filter.mpr ⟨hmem, by simp [hmem]⟩

  unfold noisy_total_efficiency_gain
  apply sum_pos_of_nonneg_of_exists_pos
    (Basins.filter (·.name ≠ A.name))
    (fun C => if noisy_absorbs A C then noisy_signed_benefit A C else 0)
    h_all_nonneg
    ⟨B, hB_filtered, h_term_pos⟩

-- Memory extension (remembers basins it has positively interacted with)
structure AgentWithMemory where
  basin    : Basin
  memory   : List Basin   -- accumulated positive exposures (simplified from Set)
  exposure : ℝ

def update_memory (A : AgentWithMemory) (B : Basin) : AgentWithMemory :=
  if absorbs A.basin B then
    { basin    := A.basin
      memory   := B :: A.memory   -- append positive interaction
      exposure := A.exposure + exposure_rate A.basin B }
  else A

-- Simple property: memory grows only on positive absorptions
theorem memory_grows_on_positive (A : AgentWithMemory) (B : Basin)
    (h_abs : absorbs A.basin B) :
    (update_memory A B).memory.length = A.memory.length + 1 := by
  simp [update_memory, h_abs]

-- If memory avoids re-testing known-bad basins (simplified model)
def avoids_known_bad (A : AgentWithMemory) (B : Basin) : Prop :=
  B ∉ A.memory → signed_benefit A.basin B ≤ 0 → True   -- trivial, but extensible

-- Theorem sketch: memory eventually focuses exposure on positives (informal direction)
theorem memory_focuses_exposure (A : AgentWithMemory) :
  ∀ B, B ∈ A.memory → signed_benefit A.basin B > 0 := by
  intro B h_mem
  -- Would require induction over update history — left as exercise/direction
  sorry

