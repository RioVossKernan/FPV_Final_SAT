/-
# Implication Graph for 2-SAT

This file defines the implication graph construction for 2-SAT formulas.
-/

import FPVFinalSAT.TwoSAT
import Mathlib.Data.List.Basic

namespace TwoSAT

-- ============ IMPLICATION GRAPH TYPES =============--

/-
An implication graph represents implications between literals.
For each clause (l1 ∨ l2), we add edges (~l1 → l2) and (~l2 → l1).
-/
structure Graph where
  edges : List (Literal × Literal)
  deriving Repr, DecidableEq

def transpose (ig : Graph) : Graph :=
  let transposedEdges := ig.edges.map (fun (u, v) => (v, u))
  ⟨transposedEdges⟩

def hasEdge (ig : Graph) (l1 l2 : Literal) : Bool :=
  (l1, l2) ∈ ig.edges

def addClause (ig : Graph) (c : Clause) : Graph :=
  ⟨(~c.lit1, c.lit2) :: (~c.lit2, c.lit1) :: ig.edges⟩

def ImplicationGraph (f : Formula) : Graph :=
  f.clauses.foldl addClause ⟨[]⟩

namespace ImplicationGraph

-- ========== REACHABILITY AND PATHS ==========

 -- A path of literals from l1 to l2 in the implication graph.
inductive isPath : Graph → Literal → Literal → List Literal → Prop
| nil {ig : Graph} {l : Literal} :
    isPath ig l l [l]
| cons {ig : Graph} {l1 l2 l3 : Literal} {path : List Literal} :
    hasEdge ig l1 l2 = true →
    isPath ig l2 l3 path →
    isPath ig l1 l3 (l1 :: path)

 -- The head of the path is the start literal.
theorem pathHeadIsStart {ig : Graph} {l1 l2 : Literal} {path : List Literal} :
    isPath ig l1 l2 path → path.head? = some l1 := by
  intro h_path
  induction h_path with
  | nil => simp
  | cons h_edge h_path_ih => simp

  -- Does a path exist from l1 to l2?
def reachable (ig : Graph) (l1 l2 : Literal) : Prop :=
  l1 = l2 ∨ ∃ (path : List Literal), isPath ig l1 l2 path

 -- Path from l1 to l2 and path from l2 to l3 implies a path from l1 to l3.
theorem path_trans {ig : Graph} {l1 l2 l3 : Literal} {path12 path23 : List Literal} :
    isPath ig l1 l2 path12 → isPath ig l2 l3 path23 →
    ∃ path13, isPath ig l1 l3 path13 := by
  intro h12 h23
  induction h12 generalizing l3 with
  | nil =>
    use path23
  | @cons a b c path' h_edge h_rest ih =>
    obtain ⟨path_rest, h_path_rest⟩ := ih h23
    use a :: path_rest
    exact isPath.cons h_edge h_path_rest


 -- Reachability is transitive.
theorem reachable_trans (ig : Graph) (l1 l2 l3 : Literal) :
    reachable ig l1 l2 → reachable ig l2 l3 → reachable ig l1 l3 := by
  intro h12 h23
  cases h12 with
  | inl h_eq =>
    rw [h_eq]
    exact h23
  | inr h_path12 =>
    cases h23 with
    | inl h_eq =>
      subst h_eq
      right
      exact h_path12
    | inr h_path23 =>
      right
      obtain ⟨path12, h_isPath12⟩ := h_path12
      obtain ⟨path23, h_isPath23⟩ := h_path23
      obtain ⟨path13, h_isPath13⟩ := path_trans h_isPath12 h_isPath23
      use path13

-- ========== STRONGLY CONNECTED COMPONENTS ==========

 -- Two literals are in the same SCC if they are mutually reachable.
def inSameSCC (ig : Graph) (l1 l2 : Literal) : Prop :=
  reachable ig l1 l2 ∧ reachable ig l2 l1

 -- An SCC is a set of literals that are all mutually reachable.
def SCC (ig : Graph) : Type :=
  { s : List Literal //
    ∀ l1 l2, l1 ∈ s → l2 ∈ s → inSameSCC ig l1 l2 }

 -- Being in the same SCC is an equivalence relation.
theorem inSameSCC_equivalence (ig : Graph) :
    Equivalence (inSameSCC ig) := by
  constructor
  · -- Reflexive
    intro l
    unfold inSameSCC
    constructor <;> (left; rfl)
  · -- Symmetric
    intro l1 l2 ⟨h1, h2⟩
    exact ⟨h2, h1⟩
  · -- Transitive
    intro l1 l2 l3 ⟨h12_fwd, h12_back⟩ ⟨h23_fwd, h23_back⟩
    constructor
    · exact reachable_trans ig l1 l2 l3 h12_fwd h23_fwd
    · exact reachable_trans ig l3 l2 l1 h23_back h12_back

-- ========== WELL-FORMEDNESS OF IMPLICATION GRAPHS ==========

/--
Well-formed implication graphs maintain the contrapositive property:
every edge l1 → l2 has a corresponding edge ~l2 → ~l1.
This is an invariant of graphs constructed via ImplicationGraph.
-/
def WellFormed (ig : Graph) : Prop :=
  ∀ l1 l2 : Literal, hasEdge ig l1 l2 = true → hasEdge ig (~l2) (~l1) = true


 -- Adding edges for a clause to a well-formed graph preserves well-formedness.
theorem addClause_WellFormed (ig : Graph) (c : Clause) (h_wf : WellFormed ig) :
    WellFormed (addClause ig c) := by
  unfold WellFormed hasEdge at h_wf
  unfold WellFormed hasEdge
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
  unfold WellFormed hasEdge
  intro l1 l2 h_edge
  simp at h_edge

 -- Graphs constructed via the ImplicationGraph function are well-formed.
theorem ImplicationGraph_wellFormed (f : Formula) : WellFormed (ImplicationGraph f) := by
  unfold ImplicationGraph
  have h_invariant : ∀ (cls : List Clause) (ig : Graph),
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
theorem contrapositive_edge (ig : Graph) (h_wf : WellFormed ig) (l1 l2 : Literal) :
    hasEdge ig l1 l2 → hasEdge ig (~l2) (~l1) := by
  intro h_edge
  unfold WellFormed at h_wf
  cases h_edge_bool : hasEdge ig l1 l2
  · simp [h_edge_bool] at h_edge
  · exact h_wf l1 l2 h_edge_bool

 -- If l1 is reachable from l2, then ~l2 is reachable from ~l1.
theorem contrapositive_reachability (ig : Graph) (h_wf : WellFormed ig)
    (l1 l2 : Literal) : reachable ig l1 l2 → reachable ig (~l2) (~l1) := by
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
      have h_contra_edge : hasEdge ig (~b) (~a) = true := by
        exact contrapositive_edge ig h_wf a b h_edge
      let h_notb_to_nota := isPath.cons h_contra_edge isPath.nil
      apply path_trans h_notc_to_notb h_notb_to_nota

-- ========== IMPLICATIONS FROM THE GRAPHS ==========

/-- Helper:
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


-- ========== KEY CORRECTNESS THEOREMS ==========

/--
MAIN THEOREM: If two literals are in the same SCC,
they must have the same truth value in any satisfying assignment.

Intuition: If l1 → l2 and l2 → l1, then l1 ↔ l2.
-/
theorem scc_same_assignment (f : Formula) (l1 l2 : Literal)
    (h_scc : inSameSCC (ImplicationGraph f) l1 l2) (a : Assignment)
    (h_sat : Assignment.isSatisfying a f) :
    Assignment.evalLiteral a l1 = Assignment.evalLiteral a l2 := by
  sorry

/--
UNSATISFIABILITY CRITERION: A formula is unsatisfiable if and only if
there exists a variable x such that x and ~x are in the same SCC.

This is the key theorem for the 2-SAT algorithm.
-/
theorem unsat_iff_var_and_neg_same_scc (f : Formula) :
    Unsatisfiable f ↔
    ∃ v : Var, inSameSCC (ImplicationGraph f) (Literal.pos v) (Literal.neg v) := by
    sorry

/--
SATISFIABILITY CRITERION: A formula is satisfiable if and only if
for every variable x, x and ~x are in different SCCs.
-/
theorem sat_iff_vars_different_sccs (f : Formula) :
    Satisfiable f ↔
    ∀ v : Var, ¬inSameSCC (ImplicationGraph f) (Literal.pos v) (Literal.neg v) := by
    sorry

end ImplicationGraph

end TwoSAT
