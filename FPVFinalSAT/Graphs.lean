/-
# Graph Data Structure

This file defines a generic directed graph structure and operations
for paths, reachability, and strongly connected components.
-/

import Mathlib.Data.List.Basic

-- ============ GRAPH STRUCTURE =============--

namespace Graphs

structure Graph (α : Type) where
  edges : List (α × α)
  deriving Repr, DecidableEq

variable {α : Type} [DecidableEq α]

def hasEdge (g : Graph α) (u v : α) : Bool :=
  (u, v) ∈ g.edges

def transpose (g : Graph α) : Graph α :=
  ⟨g.edges.map (fun (u, v) => (v, u))⟩

def neighbors (g : Graph α) (u : α) : List α :=
  g.edges.filterMap (fun (x, y) => if x = u then some y else none)

-- ========== REACHABILITY AND PATHS ==========

-- A path from u to v in the graph.
inductive isPath : Graph α → α → α → List α → Prop
| nil {g : Graph α} {u : α} :
    isPath g u u [u]
| cons {g : Graph α} {u v w : α} {path : List α} :
    hasEdge g u v = true →
    isPath g v w path →
    isPath g u w (u :: path)

-- The head of the path is the start vertex.
theorem pathHeadIsStart {g : Graph α} {u v : α} {path : List α} :
    isPath g u v path → path.head? = some u := by
  intro h_path
  induction h_path with
  | nil => simp
  | cons h_edge h_path_ih => simp

-- Does a path exist from u to v?
def reachable (g : Graph α) (u v : α) : Prop :=
  u = v ∨ ∃ (path : List α), isPath g u v path

-- Path from u to v and path from v to w implies a path from u to w.
theorem path_trans {g : Graph α} {u v w : α} {path_uv path_vw : List α} :
    isPath g u v path_uv → isPath g v w path_vw →
    ∃ path_uw, isPath g u w path_uw := by
  intro h_uv h_vw
  induction h_uv generalizing w with
  | nil =>
    use path_vw
  | @cons a b c path' h_edge h_rest ih =>
    obtain ⟨path_rest, h_path_rest⟩ := ih h_vw
    use a :: path_rest
    exact isPath.cons h_edge h_path_rest

-- Reachability is transitive.
theorem reachable_trans (g : Graph α) (u v w : α) :
    reachable g u v → reachable g v w → reachable g u w := by
  intro h_uv h_vw
  cases h_uv with
  | inl h_eq =>
    rw [h_eq]
    exact h_vw
  | inr h_path_uv =>
    cases h_vw with
    | inl h_eq =>
      subst h_eq
      right
      exact h_path_uv
    | inr h_path_vw =>
      right
      obtain ⟨path_uv, h_isPath_uv⟩ := h_path_uv
      obtain ⟨path_vw, h_isPath_vw⟩ := h_path_vw
      obtain ⟨path_uw, h_isPath_uw⟩ := path_trans h_isPath_uv h_isPath_vw
      use path_uw

-- ========== STRONGLY CONNECTED COMPONENTS ==========

-- Two vertices are in the same SCC if they are mutually reachable.
def inSameSCC (g : Graph α) (u v : α) : Prop :=
  reachable g u v ∧ reachable g v u

-- An SCC is a set of vertices that are all mutually reachable.
def SCC (g : Graph α) : Type :=
  { s : List α //
    ∀ u v, u ∈ s → v ∈ s → inSameSCC g u v }

-- Being in the same SCC is an equivalence relation.
theorem inSameSCC_equivalence (g : Graph α) :
    Equivalence (inSameSCC g) := by
  constructor
  · intro u
    unfold inSameSCC
    constructor <;> (left; rfl)
  · intro u v ⟨h1, h2⟩
    exact ⟨h2, h1⟩
  · intro u v w ⟨h_uv_fwd, h_uv_back⟩ ⟨h_vw_fwd, h_vw_back⟩
    constructor
    · exact reachable_trans g u v w h_uv_fwd h_vw_fwd
    · exact reachable_trans g w v u h_vw_back h_uv_back

end Graphs
