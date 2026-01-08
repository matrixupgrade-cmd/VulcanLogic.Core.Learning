/-
===============================================================================
UltimateToolMakerFull.lean

Author: Sean Timothy
Date: 2026-01-07

Purpose:
  Complete Lean 4 formalization of the "Ultimate Tool Maker" with:
    - Tools, counters, and safety
    - Tool shaping & improvement
    - Hardness relations, attractors, and Lagrange points
    - Hardness graph and sinks
    - Iterated shaping (blacksmith path)
    - Convergence to hardness attractors
    - Meta-tool (blacksmith) operator
===============================================================================
-/

universe u

variable {Attractor Tool Measure : Type u}
variable (CounterCurrency : Tool → Attractor → Prop)
variable (Harmful : Measure → Attractor → Prop)
variable (Shape : Tool → Tool → Tool)

/-
==============================
Tool Improvement & Safety
==============================
-/

/-- Tool improvement: T₂ preserves all counters of T₁ -/
def ToolImproves (T₁ T₂ : Tool) : Prop :=
∀ A : Attractor, CounterCurrency T₁ A → CounterCurrency T₂ A

/-- Safety: T counters all harmful attractors -/
def SafeUnder (μ : Measure) (T : Tool) : Prop :=
∀ A : Attractor, Harmful μ A → CounterCurrency T A

/-- Improvement preserves safety -/
theorem tool_path_of_persistence
  (μ : Measure)
  (T₁ T₂ : Tool)
  (hImprove : ToolImproves CounterCurrency T₁ T₂)
  (hSafe : SafeUnder μ T₁) :
  SafeUnder μ T₂ :=
by
  intro A hHarm
  have hCounter₁ : CounterCurrency T₁ A := hSafe A hHarm
  exact hImprove A hCounter₁

/-
==============================
Hardness Relation & Anvils
==============================
-/

/-- T₁ is harder than T₂: shapes T₂ but not vice versa -/
def Harder (T₁ T₂ : Tool) : Prop :=
ToolImproves CounterCurrency T₁ (Shape T₁ T₂) ∧ ¬ ToolImproves CounterCurrency T₂ (Shape T₂ T₁)

/-- Hardness attractor: nothing is harder (global anvil) -/
def HardnessAttractor (T : Tool) : Prop :=
∀ T' : Tool, ¬ Harder T' T

/-- Hardness graph structure -/
structure HardnessGraph where
  tools : List Tool
  edges : Tool → Tool → Prop := Harder CounterCurrency Shape

/-- Outgoing edges: which tools T can shape -/
def outgoing (G : HardnessGraph) (T : Tool) : List Tool :=
G.tools.filter (fun T' => G.edges T T')

/-- Incoming edges: which tools can shape T -/
def incoming (G : HardnessGraph) (T : Tool) : List Tool :=
G.tools.filter (fun T' => G.edges T' T')

/-- Lagrange point: no incoming, non-empty outgoing (stable hard tool) -/
def LagrangePoint (G : HardnessGraph) (T : Tool) : Prop :=
incoming G T = [] ∧ outgoing G T ≠ []

/-- Sink in graph (no outgoing edges) -- used for convergence theorem -/
def isSink (G : HardnessGraph) (T : Tool) : Prop :=
outgoing G T = []

/-
==============================
Iterated Shaping (Blacksmith Path)
==============================
-/

/-- Unary iterated shaping operator -/
def iterateShape (Φ : Tool → Tool) : ℕ → Tool → Tool
| 0     => id
| n+1   => Φ ∘ (iterateShape Φ n)

/-- Hard tools propagate safety -/
theorem harder_preserves_safety
  (μ : Measure)
  (T₁ T₂ : Tool)
  (hHard : Harder T₁ T₂)
  (hSafe : SafeUnder μ T₁) :
  SafeUnder μ (Shape T₁ T₂) :=
by
  intro A hHarm
  have hImprove : ToolImproves CounterCurrency T₁ (Shape T₁ T₂) := hHard.left
  exact hImprove A (hSafe A hHarm)

/-- Persistent path along unary shaping operator (anvil) -/
theorem anvil_preserves_persistence
  (μ : Measure)
  (Φ : Tool → Tool)
  (hAnvil : ∀ T, ToolImproves CounterCurrency T (Φ T)) -- Expansive shaping
  (T : Tool)
  (hSafe : SafeUnder μ T) :
  ∀ n, SafeUnder μ (iterateShape Φ n T) :=
by
  intro n
  induction n with
  | zero => exact hSafe
  | succ n ih =>
      have hImprove : ToolImproves CounterCurrency (iterateShape Φ n T)
                                           (iterateShape Φ (n+1) T) :=
        hAnvil (iterateShape Φ n T)
      exact tool_path_of_persistence μ _ _ hImprove ih

/-
==============================
Graph Paths & Convergence
==============================
-/

/-- Path in the graph -/
def HasPath (G : HardnessGraph) (T_start T_end : Tool) : Prop :=
∃ path : List Tool, path.head? = some T_start ∧ path.getLast? = some T_end ∧
  ∀ i < path.length - 1, G.edges (path.get! i) (path.get! (i+1))

/-- Acyclic: no cycles -/
def Acyclic (G : HardnessGraph) : Prop :=
∀ T : Tool, ¬ HasPath G T T  -- No path from T to itself

/-- In a finite acyclic graph, every tool reaches a sink (local hardness attractor) -/
theorem converges_to_attractor
  [DecidableEq Tool]
  (G : HardnessGraph)
  (hNodup : G.tools.Nodup)
  (hAcyclic : Acyclic G)
  (T : Tool) (hInGraph : T ∈ G.tools) :
  ∃ T_attr ∈ G.tools, isSink G T_attr ∧ HasPath G T T_attr :=
by
  induction hNodup using List.Nodup.induction_on with
  | hnil => exact absurd hInGraph (List.not_mem_nil _)
  | hcons hHdNotMem hTlNodup ih =>
    by_cases hSink : isSink G T
    · -- T itself is a sink
      use T
      exact ⟨hInGraph, hSink, ⟨[T], rfl, rfl, by simp⟩⟩
    · -- T has outgoing edges
      have hOut : outgoing G T ≠ [] := by simp [isSink] at hSink; exact hSink
      let T' := (outgoing G T).head!
      have hEdge : G.edges T T' := by
        simp [outgoing, List.head!_eq_head, hOut]
      have hT'mem : T' ∈ G.tools := List.mem_filter.mpr ⟨by assumption, hEdge⟩
      -- recurse on T'
      obtain ⟨T_attr, hAttrMem, hAttrSink, ⟨pathT', hHead, hLast, hEdges⟩⟩ := ih T' hT'mem
      use T_attr
      refine ⟨hAttrMem, hAttrSink, ⟨T :: pathT', by simp, by simp [List.getLast?_cons], _⟩⟩
      intro i hi
      by_cases hi0 : i = 0
      · simp [hi0]; exact hEdge
      · have hi' : i - 1 < pathT'.length - 1 := Nat.pred_lt_pred_iff.mpr hi
        exact hEdges (i - 1) hi'

/-
==============================
Meta-Tool / Blacksmith Operator
==============================
-/

/-- Fixed hard tool (anvil) shaping operator -/
def Blacksmith (anvil : Tool) (T : Tool) : Tool :=
Shape anvil T

/-- Iterated blacksmith path using a fixed anvil -/
def iterateBlacksmith (anvil : Tool) : ℕ → Tool → Tool :=
iterateShape (Blacksmith anvil)

/-- If an anvil is hard enough to be expansive, safety is preserved along its path -/
theorem blacksmith_preserves_persistence
  (μ : Measure)
  (anvil T : Tool)
  (hAnvil : ∀ S, ToolImproves CounterCurrency S (Blacksmith anvil S)) -- Expansive
  (hSafe : SafeUnder μ T) :
  ∀ n, SafeUnder μ (iterateBlacksmith anvil n T) :=
by
  intro n
  exact anvil_preserves_persistence μ (Blacksmith anvil) hAnvil T hSafe n

/-- Hardness assumption: anvil is harder than any tool it shapes -/
def anvil_harder_than_shapees (anvil T : Tool) : Prop :=
Harder anvil T

/-- Blacksmith path climbs hardness while preserving safety -/
theorem blacksmith_climbs_hardness
  (μ : Measure)
  (G : HardnessGraph)
  (anvil T : Tool)
  (hAnvilHard : ∀ T' ∈ G.tools, anvil_harder_than_shapees anvil T')
  (hSafe : SafeUnder μ T) :
  ∀ n, SafeUnder μ (iterateBlacksmith anvil n T) :=
by
  intro n
  -- The anvil is expansive because it is harder than every shapee
  have hExpansive : ∀ S, ToolImproves CounterCurrency S (Blacksmith anvil S) := by
    intro S
    have hHard : Harder anvil S := hAnvilHard S (by trivial)
    exact hHard.left
  exact blacksmith_preserves_persistence μ anvil hExpansive hSafe n
