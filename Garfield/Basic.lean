/- This definition was taken from graphlib -/

import Cslib.Algorithms.Lean.TimeM
import Mathlib.Logic.Relation
import Batteries.Data.Array.Scan

instance : AddZero ℕ where

namespace Graph

structure Edge (β : Type) where
  v : Nat
  w : β
deriving Repr, Inhabited, BEq

structure Vertex (α : Type) (β : Type) where
  payload : α
  adj : Array (Edge β) := #[]
deriving Repr, Inhabited, BEq

instance {α β} [Inhabited α] : Inhabited (Vertex α β) := ⟨ { payload := default } ⟩

end Graph

structure Graph (α : Type) (β : Type) : Type where
  vertices : Array (Graph.Vertex α β) := #[]
deriving Repr, BEq

namespace Graph

variable {α : Type} [Inhabited α] {β : Type}

@[grind]
def empty : Graph α β := ⟨#[]⟩

@[simp]
def edgeCount (g : Graph α β) : Nat := g.vertices.foldr (λ vertex count => vertex.adj.size + count) 0

@[simp]
def vertexCount (g : Graph α β) : Nat := g.vertices.size

@[grind]
def addVertex (g : Graph α β) (payload : α) : (Graph α β) × Nat :=
  let res := { g with vertices := g.vertices.push { payload := payload } }
  let id := res.vertexCount - 1
  (res, id)

@[grind]
def addEdge (g : Graph α β) (from' : Nat) (v : Nat) (w : β) : Graph α β := {
  g with vertices := g.vertices.modify from' (λ vertex => {
    vertex with adj := vertex.adj.push { v := v, w := w }
  } )
}

variable [BEq α]

def findVertexByPayload (g : Graph α β) (payload_a : α) : Option ℕ := g.vertices.findIdx? (fun x => x.payload == payload_a)

def findEdge (g : Graph α β) (a b : ℕ) : Option ℕ := do
  let v ← g.vertices[a]?
  v.adj.findIdx? (fun edge => edge.v == b)

end Graph

structure Walk where
  start : ℕ
  edges : Array ℕ
  end' : ℕ
deriving Repr

namespace Walk

def getVertices {α β} (w : Walk) (g : Graph α β): Array (Option ℕ) :=
  Array.scanl (fun cur edge => do (← (← g.vertices[← cur]?).adj[edge]?).v) (some w.start) w.edges

@[simp]
theorem getVertices_non_empty : Array.size (getVertices w g) > 0 := by simp [getVertices]

theorem getVertices_end_invariant {start edges end0} end1 :
    getVertices ⟨ start, edges, end0 ⟩ g = getVertices ⟨ start, edges, end1 ⟩ g := by
  simp [getVertices]

theorem getVertices_push start edges end0 end1 ei (g : Graph α β) :
    getVertices ⟨ start, edges.push ei, end0 ⟩ g
      = (getVertices ⟨ start, edges, end1 ⟩ g).push
          (Array.foldl (fun cur edge => do (← (← g.vertices[← cur]?).adj[edge]?).v) (some start) (edges.push ei)) := by
  simp only [getVertices, Array.scanl_push, Array.foldl_push]

def valid {α β} (w : Walk) (g : Graph α β) : Bool :=
  let vertices := w.getVertices g
  have h : vertices.size > 0 := by simp [vertices, getVertices, Array.size_scanl]
  vertices.all (·.filter (· < g.vertices.size) |>.isSome)
    && (vertices.back (h := h) |>.filter (· == w.end') |>.isSome)

def refl (a : ℕ) : Walk := ⟨ a, #[], a ⟩

def leg (a b : ℕ) (ei : ℕ) : Walk where
  start := a
  edges := #[ei]
  end' := b

def trans (w0 w1 : Walk) : Walk where
  start := w0.start
  edges := w0.edges ++ w1.edges
  end' := w1.end'

def findEdge {α β} (g : Graph α β) (a b : ℕ) {h : g.findEdge a b |>.isSome} : Walk where
  start := a
  edges := match h' : g.findEdge a b with
    | some ei => #[ei]
    | none => by rw [h'] at h; trivial
  end' := b

theorem _Array_induct {α} (l : Array α) (P : Array α → Prop)
    (h_nil : P #[])
    (h_cons : ∀ l a, P l → P (l.push a)) :
      P l := by sorry
    
    
theorem induct_valid {α β} (w : Walk) (g : Graph α β) (P : Walk → Prop)
    (h_refl : ∀ a, a < g.vertices.size →
      P (Walk.refl a))
    (h_step : ∀ a b ei w,
      w.valid g →
      w.start = a →
      (h_a : a < g.vertices.size) →
      (h_b : b < g.vertices.size) →
      (h_ei : ei < g.vertices[a].adj.size) →
      P (Walk.trans w ⟨ a, #[ei], b ⟩ ))
    (h_valid : w.valid g) :
      P w := by
  rcases w with ⟨ start, edges, end' ⟩
  revert end' h_valid
  apply _Array_induct edges
  · intro end' h_valid
    simp only [Walk.valid, Walk.getVertices] at h_valid
    rw! [Array.scanl_eq_singleton_iff (some start) |>.mpr ⟨ rfl, rfl ⟩] at h_valid
    simp at h_valid
    rcases h_valid with ⟨ h_start, rfl ⟩
    apply h_refl _ h_start
  · intros edges ei ih end' h_valid
    let end0 := match h : Walk.getVertices ⟨ start, edges , 0 ⟩ g |>.back with
    | some end0 => end0
    | none => by
        simp only [Walk.valid] at h_valid
        rw! [Walk.getVertices_push (end1 := 0)] at h_valid
        grind
    
    have h_edge_exists : (g.findEdge end0 end').isSome := sorry
    specialize h_step end0 end' ei ⟨ start, edges, end0 ⟩
    have h_valid' : Walk.valid ⟨ start, edges, end' ⟩ g := by
      simp [Walk.valid] at ⊢ h_valid
      rw! [Walk.getVertices_push (end1 := end')] at h_valid
      rcases h_valid with ⟨ h_valid, _ ⟩
      constructor
      · intros i h_i
        grind [h_valid i (by grind [Array.size_push])]
      · sorry

    have : Walk.findEdge g end0 end' (h := h_edge_exists) = ⟨ end0, #[ei], end' ⟩ := by
      simp [Walk.findEdge]
      rcases (Option.isSome_iff_exists.mp h_edge_exists) with ⟨ ei', h_ei' ⟩
      rw! [h_ei']; simp
      sorry

    rw [←this] at h_step; simp [Walk.trans] at h_step
    sorry

