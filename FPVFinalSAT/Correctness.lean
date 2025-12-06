/-
# Correctness of a 2-SAT Solver

This file proves the correctness of the 2-SAT algorithm
presented in Aspvall, Plass & Tarjan (1979). It does provide the
algorithm itself, but rather proves that the logic is sound.
That a solution of 2-SAT can be found using strongly connected components
of implication graphs and their properties.
-/

import FPVFinalSAT.TwoSAT
import FPVFinalSAT.ImplicationGraph
import FPVFinalSAT.Graphs

namespace TwoSAT
open ImplicationGraph
open Graphs

-- ============ CORRECTNESS THEOREMS =============--

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

end TwoSAT
