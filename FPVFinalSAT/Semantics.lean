/-
# Semantics of Implication Graphs

This file proves key semantic properties of implication graphs
used in the 2-SAT algorithm. Relating reachability in the graph
to logical implication between literals in the formula.
-/

import FPVFinalSAT.TwoSAT
import FPVFinalSAT.ImplicationGraph
import FPVFinalSAT.Graphs

namespace TwoSAT
open ImplicationGraph
open Graphs

/- Helper:
For graphs constructed by ImplicationGraph,
every edge corresponds to a clause in the formula.
-/
theorem edge_from_clause (f : Formula) (l1 l2 : Literal)
  (h_edge : hasEdge (ImplicationGraph f) l1 l2 = true) :
    ∃ c ∈ f.clauses,
      (l1 = ~c.lit1 ∧ l2 = c.lit2) ∨ (l1 = ~c.lit2 ∧ l2 = c.lit1) := by
  unfold ImplicationGraph at h_edge
  -- prove that edges in fold come from clauses
  have h_edge_from_fold : ∀ (cls : List Clause) (ig : LiteralGraph),
    hasEdge (cls.foldl addClause ig) l1 l2 = true →
    (hasEdge ig l1 l2 = true ∨
     ∃ c ∈ cls, (l1 = ~c.lit1 ∧ l2 = c.lit2) ∨ (l1 = ~c.lit2 ∧ l2 = c.lit1)) := by
    intro cls ig
    induction cls generalizing ig with
    | nil =>
      intro h
      left
      exact h
    | cons c rest ih =>
      intro h
      simp only [List.foldl] at h
      have h_after_c := ih (addClause ig c) h
      cases h_after_c with
      | inl h_in_after_c =>
        unfold addClause hasEdge at h_in_after_c
        simp only [decide_eq_true_eq, List.mem_cons] at h_in_after_c
        rcases h_in_after_c with h1 | h2 | h3
        · cases h1
          right
          use c
          simp
        · cases h2
          right
          use c
          simp
        · left
          unfold hasEdge
          simp
          exact h3
      | inr h_from_rest =>
        right
        obtain ⟨c', h_c_in_rest, h_props⟩ := h_from_rest
        use c'
        constructor
        · right
          exact h_c_in_rest
        · exact h_props
  have h_from_clauses := h_edge_from_fold f.clauses ⟨[]⟩ h_edge
  cases h_from_clauses with
  | inl h_in_empty =>
    unfold hasEdge at h_in_empty
    simp at h_in_empty
  | inr h =>
    exact h

/--
If there's an edge l1 → l2,
then l1 implies l2 under any satisfying assignment.
-/
theorem edge_implies (f : Formula) (l1 l2 : Literal) (a : Assignment)
    (h_edge : hasEdge (ImplicationGraph f) l1 l2 = true)
    (h_sat : Assignment.isSatisfying a f) :
    (h_l1_true : Assignment.evalLiteral a l1 = true) → Assignment.evalLiteral a l2 = true := by
  intro h_l1_true
  obtain ⟨c, h_c_in_clauses, h_edge_type⟩ := edge_from_clause f l1 l2 h_edge
  unfold Assignment.isSatisfying Assignment.evalFormula at h_sat
  rw [List.all_eq_true] at h_sat
  have h_c_sat := h_sat c h_c_in_clauses
  cases h_edge_type with
  | inl h_type1 =>
    obtain ⟨h_l1_eq, h_l2_eq⟩ := h_type1
    rw [h_l2_eq]
    unfold Assignment.evalClause at h_c_sat
    unfold Assignment.evalLiteral at h_c_sat
    rw [h_l1_eq] at h_l1_true
    unfold Assignment.evalLiteral at h_l1_true
    simp at h_l1_true
    unfold Assignment.evalLiteral
    by_cases h1 : c.lit1.polarity = a c.lit1.var
    · rw [h1] at h_l1_true
      simp at h_l1_true
    · simp only [h1] at h_c_sat
      cases h_decide : decide (c.lit2.polarity = a c.lit2.var)
      · simp [h_decide] at h_c_sat
      · rfl
  | inr h_type2 =>
    obtain ⟨h_l1_eq, h_l2_eq⟩ := h_type2
    rw [h_l2_eq]
    unfold Assignment.evalClause at h_c_sat
    unfold Assignment.evalLiteral at h_c_sat
    rw [h_l1_eq] at h_l1_true
    unfold Assignment.evalLiteral at h_l1_true
    simp at h_l1_true
    unfold Assignment.evalLiteral
    by_cases h2 : c.lit2.polarity = a c.lit2.var
    · rw [h2] at h_l1_true
      simp at h_l1_true
    · simp only [h2] at h_c_sat
      cases h_decide : decide (c.lit1.polarity = a c.lit1.var)
      · simp [h_decide] at h_c_sat
      · rfl

/--
If there's a path l1 → ... → l2 in the implication graph,
then l1 implies l2 under any satisfying assignment.
-/
theorem path_implies (f : Formula) (l1 l2 : Literal) (path : List Literal)
    (h_path : isPath (ImplicationGraph f) l1 l2 path) (a : Assignment)
    (h_sat : Assignment.isSatisfying a f) :
    Assignment.evalLiteral a l1 = true → Assignment.evalLiteral a l2 = true := by
  intro h_l1_true
  induction h_path with
  | nil => exact h_l1_true
  | @cons la lb lc path' h_edge h_rest ih =>
    have h_lb_true : Assignment.evalLiteral a lb = true := by
      exact edge_implies f la lb a h_edge h_sat h_l1_true
    exact ih h_lb_true

/--
If l1 is reachable from l2 in the implication graph,
then l1 implies l2 under any satisfying assignment.
-/
theorem reachable_implies (f : Formula) (l1 l2 : Literal) (a : Assignment)
    (h_reach : reachable (ImplicationGraph f) l1 l2)
    (h_sat : Assignment.isSatisfying a f) :
    Assignment.evalLiteral a l1 = true → Assignment.evalLiteral a l2 = true := by
  intro h_l1_true
  cases h_reach with
  | inl h_eq =>
    rw [← h_eq]
    exact h_l1_true
  | inr h_path =>
    obtain ⟨path, h_isPath⟩ := h_path
    exact path_implies f l1 l2 path h_isPath a h_sat h_l1_true

end TwoSAT
