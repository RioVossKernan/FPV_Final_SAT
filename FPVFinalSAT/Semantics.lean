/-
# Semantics of Implication Graphs

This file proves key semantic properties of implication graphs
used in the 2-SAT algorithm. Mostly, how reachability in the graph
corresponds to logical implication between literals in the formula.
-/

import FPVFinalSAT.TwoSAT
import FPVFinalSAT.ImplicationGraph
import FPVFinalSAT.Graphs

namespace TwoSAT
open ImplicationGraph
open Graphs

/- Helper:
For graphs constructed via ImplicationGraph,
every edge corresponds to a clause in the formula.
-/
theorem edge_from_clause (f : Formula) (l1 l2 : Literal)
  (h_edge : hasEdge (ImplicationGraph f) l1 l2 = true) :
    ∃ c ∈ f.clauses,
      (l1 = ~c.lit1 ∧ l2 = c.lit2) ∨ (l1 = ~c.lit2 ∧ l2 = c.lit1) := by
  unfold ImplicationGraph at h_edge
  -- Prove by induction that edges in foldl come from clauses
  have h_edge_from_fold : ∀ (cls : List Clause) (ig0 : Graph),
    hasEdge (cls.foldl addClause ig0) l1 l2 = true →
    (hasEdge ig0 l1 l2 = true ∨
     ∃ c ∈ cls, (l1 = ~c.lit1 ∧ l2 = c.lit2) ∨ (l1 = ~c.lit2 ∧ l2 = c.lit1)) := by
    intro cls ig0
    induction cls generalizing ig0 with
    | nil =>
      intro h
      left
      exact h
    | cons c rest ih =>
      intro h
      simp only [List.foldl] at h
      have h_after_c := ih (addClause ig0 c) h
      cases h_after_c with
      | inl h_in_after_c =>
        -- Edge is in (addClause ig0 c)
        unfold addClause hasEdge at h_in_after_c
        simp only [decide_eq_true_eq, List.mem_cons] at h_in_after_c
        rcases h_in_after_c with h1 | h2 | h3
        · -- Edge is (~c.lit1, c.lit2)
          cases h1
          right
          use c
          simp
        · -- Edge is (~c.lit2, c.lit1)
          cases h2
          right
          use c
          simp
        · -- Edge was in ig0.edges
          left
          unfold hasEdge
          simp
          exact h3
      | inr h_from_rest =>
        -- Edge comes from rest
        right
        obtain ⟨c', h_c_in_rest, h_props⟩ := h_from_rest
        use c'
        constructor
        · right
          exact h_c_in_rest
        · exact h_props
  -- Apply to our specific case
  have h_from_clauses := h_edge_from_fold f.clauses ⟨[]⟩ h_edge
  cases h_from_clauses with
  | inl h_in_empty =>
    -- Edge in empty graph is impossible
    unfold hasEdge at h_in_empty
    simp at h_in_empty
  | inr h =>
    exact h

/--
Helper: For graphs constructed from formulas, if there's an edge l1 → l2,
and l1 is true under a satisfying assignment, then l2 must also be true.
-/
theorem edge_implies_from_formula (f : Formula) (l1 l2 : Literal) (a : Assignment)
    (h_edge : hasEdge (ImplicationGraph f) l1 l2 = true)
    (h_sat : Assignment.isSatisfying a f)
    (h_l1_true : Assignment.evalLiteral a l1 = true) :
    Assignment.evalLiteral a l2 = true := by
  -- Get the clause from which this edge comes
  obtain ⟨c, h_c_in_clauses, h_edge_type⟩ := edge_from_clause f l1 l2 h_edge
  -- The clause c is in the formula, so it's satisfied
  unfold Assignment.isSatisfying Assignment.evalFormula at h_sat
  rw [List.all_eq_true] at h_sat
  have h_c_sat := h_sat c h_c_in_clauses
  -- The edge is either (~c.lit1 → c.lit2) or (~c.lit2 → c.lit1)
  cases h_edge_type with
  | inl h_type1 =>
    -- l1 = ~c.lit1 and l2 = c.lit2
    obtain ⟨h_l1_eq, h_l2_eq⟩ := h_type1
    rw [h_l2_eq]
    -- Clause c = (c.lit1 ∨ c.lit2) is satisfied
    unfold Assignment.evalClause at h_c_sat
    unfold Assignment.evalLiteral at h_c_sat
    -- l1 = ~c.lit1 is true, so c.lit1 is false
    rw [h_l1_eq] at h_l1_true
    unfold Assignment.evalLiteral at h_l1_true
    simp at h_l1_true
    -- Since c.lit1 is false (h_l1_true) and the clause is satisfied (h_c_sat),
    -- c.lit2 must be true
    unfold Assignment.evalLiteral
    by_cases h1 : c.lit1.polarity = a c.lit1.var
    · -- c.lit1 is true, contradiction with h_l1_true
      rw [h1] at h_l1_true
      simp at h_l1_true
    · -- c.lit1 is false, so c.lit2 must be true
      simp only [h1] at h_c_sat
      cases h_decide : decide (c.lit2.polarity = a c.lit2.var)
      · simp [h_decide] at h_c_sat
      · rfl
  | inr h_type2 =>
    -- l1 = ~c.lit2 and l2 = c.lit1
    obtain ⟨h_l1_eq, h_l2_eq⟩ := h_type2
    rw [h_l2_eq]
    -- Clause c = (c.lit1 ∨ c.lit2) is satisfied
    unfold Assignment.evalClause at h_c_sat
    unfold Assignment.evalLiteral at h_c_sat
    -- l1 = ~c.lit2 is true, so c.lit2 is false
    rw [h_l1_eq] at h_l1_true
    unfold Assignment.evalLiteral at h_l1_true
    simp at h_l1_true
    -- Since c.lit2 is false (h_l1_true) and the clause is satisfied (h_c_sat),
    -- c.lit1 must be true
    unfold Assignment.evalLiteral
    by_cases h2 : c.lit2.polarity = a c.lit2.var
    · -- c.lit2 is true, contradiction with h_l1_true
      rw [h2] at h_l1_true
      simp at h_l1_true
    · -- c.lit2 is false, so c.lit1 must be true
      simp only [h2] at h_c_sat
      cases h_decide : decide (c.lit1.polarity = a c.lit1.var)
      · simp [h_decide] at h_c_sat
      · rfl

/--
Helper: If there's an edge l1 → l2 in the implication graph for a formula,
and l1 is true under some assignment that satisfies the formula,
then l2 must also be true.

This is now proven directly using edge_implies_from_formula!
-/
theorem edge_implies (f : Formula) (l1 l2 : Literal) (a : Assignment)
    (h_edge : hasEdge (ImplicationGraph f) l1 l2 = true)
    (h_sat : Assignment.isSatisfying a f)
    (h_l1_true : Assignment.evalLiteral a l1 = true) :
    Assignment.evalLiteral a l2 = true :=
  edge_implies_from_formula f l1 l2 a h_edge h_sat h_l1_true

/--
Helper: If there's a path from l1 to l2 in the implication graph,
and l1 is true under some assignment that satisfies the formula,
then l2 must also be true.

This is the key semantic property: reachability in the graph
corresponds to logical implication.
-/
theorem path_implies (f : Formula) (l1 l2 : Literal) (path : List Literal)
    (h_path : isPath (ImplicationGraph f) l1 l2 path) (a : Assignment)
    (h_sat : Assignment.isSatisfying a f)
    (h_l1_true : Assignment.evalLiteral a l1 = true) :
    Assignment.evalLiteral a l2 = true := by
  induction h_path with
  | nil =>
    -- l1 = l2, so if l1 is true, then l2 is true
    exact h_l1_true
  | cons h_edge h_rest ih =>
    -- We have l1 → l_mid and a path l_mid → ... → l2
    -- If l1 is true, then l_mid is true (by edge_implies)
    -- If l_mid is true, then l2 is true (by IH)
    rename_i la lb lc path'
    have h_lb_true : Assignment.evalLiteral a lb = true := by
      exact edge_implies f la lb a h_edge h_sat h_l1_true
    exact ih h_lb_true

/--
If l1 is reachable from l2 in the implication graph,
and l1 is true under some assignment that satisfies the formula,
then l2 must also be true.
-/
theorem reachable_implies (f : Formula) (l1 l2 : Literal) (a : Assignment)
    (h_reach : reachable (ImplicationGraph f) l1 l2)
    (h_sat : Assignment.isSatisfying a f)
    (h_l1_true : Assignment.evalLiteral a l1 = true) :
    Assignment.evalLiteral a l2 = true := by
  cases h_reach with
  | inl h_eq =>
    -- l1 = l2
    rw [← h_eq]
    exact h_l1_true
  | inr h_path =>
    -- There exists a path from l1 to l2
    obtain ⟨path, h_isPath⟩ := h_path
    exact path_implies f l1 l2 path h_isPath a h_sat h_l1_true

end TwoSAT
