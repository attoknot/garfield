/- This definition was taken from graphlib -/

import Cslib.Algorithms.Lean.TimeM
import Mathlib.Logic.Relation
import Batteries.Data.Array.Scan
import Mathlib.Order.Defs.LinearOrder
import Mathlib.Order.Fin.Basic
import Mathlib.Algebra.Group.Even
import Mathlib.Algebra.Group.Nat.Even

instance : AddZero ℕ where

structure Graph (α : Type) where
  -- for now we = wv = Unit
  -- number of edges between a and b. the signature become clearer when we introduce weights
  edges : (a b : α) → ℕ

def Graph.toList {n : Nat} (g : Graph (Fin n)) : List (Fin n × Fin n × Nat) :=
  let vertices := List.ofFn (fun i : Fin n => i)
  vertices.flatMap fun u =>
    vertices.flatMap fun v =>
      let edgeCount := g.edges u v
      List.ofFn (fun i : Fin edgeCount => (u, v, i.val))

instance : Repr (Graph (Fin n)) where
  reprPrec := reprPrec ∘ Graph.toList

-- todo: remove simp in the future
@[simp]
def Graph.empty : Graph (Fin 0) where
  edges a b := by cases a; lia

@[simp]
def Graph.addVertex {n : ℕ} (g : Graph (Fin n)) : Graph (Fin (n.succ)) where
  edges a b :=
    if h : a = n ∨ b = n
    then 0
    else g.edges ⟨ a.val, by lia ⟩ ⟨ b.val, by lia ⟩

@[simp]
def Graph.addEdge {n : ℕ} (g : Graph (Fin n)) (a b : Fin n) : Graph (Fin n) where
  edges a' b' :=
    if _ : a = a' && b = b'
    then g.edges a' b' + 1
    else g.edges a' b'

def Edge {α} (g : Graph α) (a b : α) : Type :=
  Fin (g.edges a b)

inductive Walk {α} (g : Graph α) : α → α → Type
| nil : {a : α} → Walk g a a
| cons : {a b c : α} → Walk g a b → Edge g b c → Walk g a c

namespace Walk

variable {α : Type} {g : Graph α}

-- important: doesn't include the last vertex. todo: add a new property length and appropriate lemmas
def vertices {a c : α} (w : Walk g a c) : List α := match w with
| nil => []
| cons w edge => Walk.vertices w ++ [c]

def isPath {a c : α} (w : Walk g a c) : Prop := w.vertices.Nodup

def isCycle {a : α} (w : Walk g a a) : Bool :=
  match w with
  | .nil => true
  | _ => false

end Walk

structure Path {α} (g : Graph α) (a b : α) where
  walk : Walk g a b
  is_path : walk.isPath

namespace Graph

variable {α : Type} (g : Graph α)

-- simple classes

def isLoopless : Prop :=
  ∀ a : α, g.edges a a = 0

def isMultiless : Prop :=
  ∀ a b : α, g.edges a b < 0

def isSimple : Prop :=
  g.isLoopless ∧ g.isMultiless

def isUndirected : Prop :=
  ∀ a b : α, g.edges a b = g.edges b a

@[simp, grind]
def Reachable (a b : α) : Prop := Nonempty (Walk g a b)

def isConnected : Prop := g.isUndirected ∧ ∀ a b : α, Reachable g a b

def prepend_walk {a b c : α} (x : Edge g a b) (w : Walk g b c) : Walk g a c :=
  match w with
  | .nil => Walk.cons Walk.nil x
  | .cons w edge => Walk.cons (prepend_walk x w) edge

def reverse_edge {a b : α}
    {h_undirected : g.isUndirected}
    (edge : Edge g a b) :
    Edge g b a := by
  dsimp [Edge] at ⊢ edge
  rw [h_undirected b a]
  exact edge

def reverse_walk {a b : α}
    {h_undirected : g.isUndirected}
    (w : Walk g a b) :
    Walk g b a :=
  match w with
  | .nil => Walk.nil
  | .cons (b := b) (c := c) w edge =>
    let edge' : Edge g c b := reverse_edge g (h_undirected := h_undirected) edge
    prepend_walk g edge' (reverse_walk (h_undirected := h_undirected) w)

theorem isConnected_of_isUndirected [LinearOrder α]
    (h_undirected : g.isUndirected)
    (h : (∀ a b : α, a < b → Reachable g a b)) :
    g.isConnected := by
  refine ⟨ h_undirected, ?_ ⟩
  intros a b
  rcases lt_trichotomy a b with a_lt_b | a_eq_b | a_gt_b
  · apply h; assumption
  · rw [a_eq_b]
    use Walk.nil
  · rcases h b a (by lia) with ⟨ walk ⟩
    use reverse_walk g (h_undirected := h_undirected) walk

def isAcyclic := ∀ (a : α) (w : Walk g a a), !w.isCycle

def Coloring (k : ℕ) (color : α → Fin k) : Prop :=
  ∀ a b : α, Edge g a b → color a ≠ color b

def isBipartite := ∃ color, Coloring g 2 color

theorem isBipartite_isLoopless {color}
    {h_bipartite : Coloring g 2 color} :
    g.isLoopless := by
  dsimp [Coloring, isLoopless] at ⊢ h_bipartite
  intros a
  cases h : g.edges a a with
  | zero => rfl
  | succ n =>
    specialize h_bipartite a a ?_ rfl
    · use 0; lia
    trivial

theorem isBipartite_walk_parity {a b : α} {color}
    {h_bipartite : Coloring g 2 color}
    (w : Walk g a b) :
    Even w.vertices.length ↔ color a = color b := by
  suffices ∀ n, w.vertices.length = n → (Even w.vertices.length ↔ color a = color b) by grind
  dsimp [Coloring] at h_bipartite
  intros n
  induction n generalizing a b w with
  | zero =>
    cases w
    · intro h; rw [h]; simp
    · simp [Walk.vertices]
  | succ n ih =>
    cases w with
    | nil => simp [Walk.vertices]
    | @cons b' _ w edge  =>
      simp [Walk.vertices]
      intros h
      specialize @ih a b' w h
      rw [h] at ⊢ ih
      constructor
      · show Even (n + 1) → color a = color b
        intro h_even
        have : ¬ Even n := Nat.even_add_one.mp h_even
        have : color a ≠ color b' := by tauto
        have : color b' ≠ color b := h_bipartite _ _ edge
        have : ∀ a b c : Fin 2, a ≠ b → b ≠ c → a = c := by lia
        tauto
      · show color a = color b → Even (n + 1)
        intro h_color_eq
        have : color b' ≠ color b := h_bipartite _ _ edge
        have : color a ≠ color b' := by grind only
        have : ¬ Even n := by grind only
        grind

def Shortest {a b : α} (w : Walk g a b) := ∀ w' : Walk g a b, w.vertices.length ≤ w'.vertices.length

def Distance (a b : α) (n : ℕ) := ∃ w : Walk g a b, w.vertices.length = n ∧ Shortest g w

end Graph

section

def g : Graph (Fin 2) := Graph.empty.addVertex.addVertex |>.addEdge 1 0 |>.addEdge 0 1

example : g.isConnected := by
  apply Graph.isConnected_of_isUndirected
  · show ∀ a b : Fin 2, g.edges a b = g.edges b a
    rintro ⟨ _ | _ | a, ha ⟩ ⟨ _ | _ | b, hb ⟩ <;> try lia
    all_goals simp [g]
  · rintro ⟨ _ | _ | a, ha ⟩ ⟨ _ | _ | b, hb ⟩ _ <;> try lia
    use Walk.cons (b := 0) ?_ ?_
    · use Walk.nil
    · use 0; simp [g]

example : g.Distance 0 1 1 := by
  dsimp [Graph.Distance, Graph.Shortest]
  let w : Walk g 0 1 := Walk.cons (b := 0) Walk.nil ⟨0, by simp [g]⟩
  use w
  constructor
  · simp [w, Walk.vertices]
  intros w'
  cases w' with
  | cons w' edge => cases w' with
    | cons w' edge2 => simp [w, Walk.vertices]
    | nil => rfl

end
