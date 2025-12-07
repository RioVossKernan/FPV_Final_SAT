/-
# Implication Graph for 2-SAT

This file defines the implication graph construction for 2-SAT formulas.
-/

import FPVFinalSAT.TwoSAT
import FPVFinalSAT.Graphs
import Mathlib.Data.List.Basic

namespace TwoSAT

-- ============ IMPLICATION GRAPH CONSTRUCTION =============--

/-
An implication graph represents implications between literals.
For each clause (l1 ∨ l2), we add edges (~l1 → l2) and (~l2 → l1).
-/

def LiteralGraph := Graphs.Graph Literal

def addClause (ig : LiteralGraph) (c : Clause) : LiteralGraph :=
  ⟨(~c.lit1, c.lit2) :: (~c.lit2, c.lit1) :: ig.edges⟩

def ImplicationGraph (f : Formula) : LiteralGraph :=
  f.clauses.foldl addClause ⟨[]⟩

namespace ImplicationGraph

-- ========== WELL-FORMEDNESS OF IMPLICATION GRAPHS ==========

/--
Well-formed implication graphs maintain the contrapositive property:
every edge l1 → l2 has a corresponding edge ~l2 → ~l1.
This is an invariant of graphs constructed via ImplicationGraph.
-/
def WellFormed (ig : LiteralGraph) : Prop :=
  ∀ l1 l2 : Literal, Graphs.hasEdge ig l1 l2 = true → Graphs.hasEdge ig (~l2) (~l1) = true


 -- Adding edges for a clause to a well-formed graph preserves well-formedness.
theorem addClause_WellFormed (ig : LiteralGraph) (c : Clause) (h_wf : WellFormed ig) :
    WellFormed (addClause ig c) := by
  unfold WellFormed Graphs.hasEdge at h_wf
  unfold WellFormed Graphs.hasEdge
  intro l1 l2 h_edge
  unfold addClause at h_edge
  unfold addClause
  simp only [decide_eq_true_eq, List.mem_cons] at h_edge
  simp
  rcases h_edge with h1 | h2 | h3
  · cases h1
    right
    left
    simp
  · cases h2
    left
    simp
  · right
    right
    have h_contra: decide ((~l2, ~l1) ∈ ig.edges) = true := by
      apply h_wf
      simp
      assumption
    simp at h_contra
    assumption

 -- An empty graph is well-formed.
theorem empty_graph_wellFormed :
    WellFormed ⟨[]⟩ := by
  unfold WellFormed Graphs.hasEdge
  intro l1 l2 h_edge
  simp at h_edge

 -- Graphs constructed via the ImplicationGraph function are well-formed.
theorem ImplicationGraph_wellFormed (f : Formula) : WellFormed (ImplicationGraph f) := by
  unfold ImplicationGraph
  have h_invariant : ∀ (cls : List Clause) (ig : LiteralGraph),
    WellFormed ig → WellFormed (cls.foldl addClause ig) := by
    intro cls ig
    induction cls generalizing ig with
    | nil =>
      intro h_wf_ig
      simp
      exact h_wf_ig
    | cons c rest ih =>
      intro h_wf_ig
      simp only [List.foldl]
      have h_after_c : WellFormed (addClause ig c) :=
        addClause_WellFormed ig c h_wf_ig
      exact ih (addClause ig c) h_after_c

  exact h_invariant f.clauses ⟨[]⟩ empty_graph_wellFormed

 -- If there's an edge l1 → l2 in a well-formed graph, then ~l2 → ~l1.
theorem contrapositive_edge (ig : LiteralGraph) (h_wf : WellFormed ig) (l1 l2 : Literal) :
    Graphs.hasEdge ig l1 l2 → Graphs.hasEdge ig (~l2) (~l1) := by
  intro h_edge
  unfold WellFormed at h_wf
  cases h_edge_bool : Graphs.hasEdge ig l1 l2
  · simp [h_edge_bool] at h_edge
  · exact h_wf l1 l2 h_edge_bool

 -- If l1 is reachable from l2, then ~l2 is reachable from ~l1.
theorem contrapositive_reachability (ig : LiteralGraph) (h_wf : WellFormed ig)
    (l1 l2 : Literal) : Graphs.reachable ig l1 l2 → Graphs.reachable ig (~l2) (~l1) := by
  intro h_reach
  cases h_reach with
  | inl h_eq =>
    -- If l1 = l2, then ~l2 = ~l1
    have h_neg_eq : ~l2 = ~l1 := by rw [h_eq]
    left
    exact h_neg_eq
  | inr h_path =>
    right
    obtain ⟨path, h_isPath⟩ := h_path
    induction h_isPath with
    | @nil a =>
      use [~a]
      constructor
    | @cons a b c path h_edge h_rest ih =>
      obtain ⟨_, h_notc_to_notb⟩ := ih
      have h_contra_edge : Graphs.hasEdge ig (~b) (~a) = true := by
        exact contrapositive_edge ig h_wf a b h_edge
      let h_notb_to_nota := Graphs.isPath.cons h_contra_edge Graphs.isPath.nil
      apply Graphs.path_trans h_notc_to_notb h_notb_to_nota

end ImplicationGraph

end TwoSAT
