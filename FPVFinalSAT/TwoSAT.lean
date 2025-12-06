
/-
# 2-SAT

This file defines the basic data structures
and operations for 2-SAT
-/

import Mathlib.Data.List.Basic

namespace TwoSAT

--============= BASIC 2SAT TYPES =============--

-- Variables are represented as nats (ex: x1, x2, x3)
abbrev Var := Nat

-- Variable that is either positive or negative
structure Literal where
  var : Var
  polarity : Bool
  deriving Repr, DecidableEq

-- A disjunction of two literals (l1 ∨ l2)
structure Clause where
  lit1 : Literal
  lit2 : Literal
  deriving Repr, DecidableEq

-- A conjunction of clauses (c1 ∧ c2 ∧ ... ∧ cn)
structure Formula where
  clauses : List Clause
  deriving Repr, DecidableEq

-- An assignment function maps vars to True/False
def Assignment := Var → Bool

------ LITERAL HELPERS ------

namespace Literal

def pos (v : Var) : Literal := ⟨v, true⟩
def neg (v : Var) : Literal := ⟨v, false⟩

@[simp]
def negate (l : Literal) : Literal := ⟨l.var, !l.polarity⟩
prefix:max "~" => negate

-- Same variable but opposite polarity
@[simp]
def isComplementary (l₁ l₂ : Literal) : Bool :=
  l₁.var = l₂.var && l₁.polarity != l₂.polarity

def isPositive (l : Literal) : Bool := l.polarity
def isNegative (l : Literal) : Bool := !l.polarity

------ LITERAL THEOREMS ------
@[simp]
theorem negate_negate (l : Literal) : ~~l = l := by
  cases l with
  | mk v p => simp

@[simp]
theorem complementary_of_negate (l : Literal) : isComplementary l ~l = true := by
  cases l with | mk v p =>
  simp

@[simp]
theorem negate_of_complementary (l₁ l₂ : Literal) :
    isComplementary l₁ l₂ = true → l₂ = ~l₁ ∨ l₁ = ~l₂ := by
  cases l₁ with | mk v₁ p₁ =>
  cases l₂ with | mk v₂ p₂ =>
  simp
  intro h_var h_pol
  cases p₁ <;> cases p₂ <;> grind

end Literal


------ CLAUSE HELPERS ------

namespace Clause

/--
A tautology contains a literal and its negation.
For example: (x ∨ ¬x) is always true.
-/
@[simp]
def isTautology (c : Clause) : Bool :=
  Literal.isComplementary c.lit1 c.lit2

def vars (c : Clause) : List Var :=
  [c.lit1.var, c.lit2.var]

def literals (c : Clause) : List Literal :=
  [c.lit1, c.lit2]

end Clause


------ FORMULA HELPERS ------

namespace Formula

@[simp]
def empty : Formula := ⟨[]⟩

def singleton (c : Clause) : Formula := ⟨[c]⟩

def vars (f : Formula) : List Var :=
  (f.clauses.flatMap Clause.vars).eraseDups

def numClauses (f : Formula) : Nat :=
  f.clauses.length

def numVars (f : Formula) : Nat :=
  f.vars.length

/--
Remove all tautological clauses from the formula.
Tautologies are always satisfied so don't affect satisfiability.
-/
@[simp]
def removeTautologies (f : Formula) : Formula :=
  ⟨f.clauses.filter (fun c => !c.isTautology)⟩

end Formula


------ ASSIGNMENTS HELPERS ------

namespace Assignment
/-
we "evaluate" under an assignment by checking
if the literal/clause/formula is true after substituting
the assignment values for each variable.
-/

def evalLiteral (a : Assignment) (l : Literal) : Bool :=
  l.polarity = a l.var

def evalClause (a : Assignment) (c : Clause) : Bool :=
  evalLiteral a c.lit1 || evalLiteral a c.lit2

def evalFormula (a : Assignment) (f : Formula) : Bool :=
  f.clauses.all (evalClause a)

def isSatisfying (a : Assignment) (f : Formula) : Prop :=
  evalFormula a f = true

end Assignment


------ SATISFIABILITY ------

-- A formula is SAT if there exists an assignment that satisfies it.
def Satisfiable (f : Formula) : Prop :=
  ∃ a : Assignment, Assignment.isSatisfying a f

-- A formula is UNSAT if no assignment satisfies it.
def Unsatisfiable (f : Formula) : Prop :=
  ∀ a : Assignment, Assignment.evalFormula a f = false

------ SATISFIABILITY THEOREMS ------

-- Any formula is either satisfiable or unsatisfiable
theorem satisfiable_or_unsatisfiable (f : Formula) :
    Satisfiable f ∨ Unsatisfiable f := by
  by_cases h : Satisfiable f
  · left
    exact h
  · right
    unfold Unsatisfiable
    unfold Satisfiable at h
    have h_nosat : ∀ a : Assignment, ¬a.isSatisfying f := by
      intro a h_sat
      exact h ⟨a, h_sat⟩
    unfold Assignment.isSatisfying at h_nosat
    grind

-- The empty formula is satisfiable
theorem empty_satisfiable : Satisfiable Formula.empty := by
  use (fun _ => true)
  simp [Formula.empty, Assignment.isSatisfying, Assignment.evalFormula]

-- Removing tautologies preserves satisfiability.
-- This turned out to be unnecessary but interesting nonetheless.
theorem removeTautologies_preserves_sat (f : Formula) :
    Satisfiable f ↔ Satisfiable (f.removeTautologies) := by
  constructor
  · -- forward
    intro ⟨a, h_sat⟩
    use a
    simp only [Assignment.isSatisfying,
              Assignment.evalFormula,
              Formula.removeTautologies,
              List.all_eq_true]
    intro c h_c_mem
    have h_c_in_f: c ∈ f.clauses := by
      rw [List.mem_filter] at h_c_mem
      exact h_c_mem.left
    simp [Assignment.isSatisfying, Assignment.evalFormula, List.all_eq_true] at h_sat
    exact h_sat c h_c_in_f
  · -- backward
    intro ⟨a, h_sat⟩
    use a
    simp only [Assignment.isSatisfying, Assignment.evalFormula, List.all_eq_true]
    intro c h_c_mem
    by_cases h_taut : c.isTautology = true
    · -- c is a tautology: always satisfied
      cases c with | mk l1 l2 =>
      simp only [Clause.isTautology, Literal.isComplementary] at h_taut
      simp only [Bool.and_eq_true, decide_eq_true_eq] at h_taut
      obtain ⟨h_var_eq, h_pol_ne⟩ := h_taut
      simp only [Assignment.evalClause, Assignment.evalLiteral]
      rw [h_var_eq]
      cases h1 : l1.polarity
      · cases h2 : l2.polarity
        · simp [h1, h2] at h_pol_ne
        · simp
      · cases h2 : l2.polarity
        · simp
        · simp [h1, h2] at h_pol_ne
    · -- c is not a tautology: in the filtered formula
      simp only [Assignment.isSatisfying,
                 Assignment.evalFormula,
                 Formula.removeTautologies,
                 List.all_eq_true] at h_sat
      apply h_sat
      rw [List.mem_filter]
      constructor
      · exact h_c_mem
      · cases h_iso : c.isTautology
        · rfl
        · exfalso
          rw [h_iso] at h_taut
          simp at h_taut


end TwoSAT
