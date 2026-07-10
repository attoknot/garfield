/- This definition was taken from graphlib -/

import Cslib.Algorithms.Lean.TimeM
import Mathlib.Logic.Relation

instance : AddZero ℕ where

namespace Graph

structure Edge (β : Type) where
  v : Nat
  w : β
deriving Repr

structure Vertex (α : Type) (β : Type) where
  payload : α
  adj : Array (Edge β) := #[]
deriving Repr

instance {α β} [Inhabited α] : Inhabited (Vertex α β) := ⟨ { payload := default } ⟩

end Graph

structure Graph (α : Type) (β : Type) : Type where
  vertices : Array (Graph.Vertex α β) := #[]
deriving Repr

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

inductive EdgeRel (g : Graph α β) : ℕ → ℕ → Type where
| mk a ei :
    (h_a : a < g.vertices.size) →
    (h_ei : ei < g.vertices[a].adj.size) →
    EdgeRel g a g.vertices[a].adj[ei].v
deriving Repr

inductive Walk (g : Graph α β) : ℕ → ℕ → Type where
| refl {a} : g.Walk a a
| step {a b c} : g.EdgeRel a b → g.Walk b c → g.Walk a c
deriving Repr

variable [BEq α]

def findVertexByPayload (g : Graph α β) (payload_a : α) : Option ℕ := g.vertices.findIdx? (fun x => x.payload == payload_a)

def findEdge (g : Graph α β) (a b : ℕ) : Option ℕ := do
  let v ← g.vertices[a]?
  v.adj.findIdx? (fun edge => edge.v == b)

def findEdgeRel(g : Graph α β) (a b : ℕ)
  (h_a : a < g.vertices.size)
  (h_e : (g.findEdge a b).isSome) : EdgeRel g a b := by
  cases h_ei : findEdge g a b with
  | none => rw [h_ei] at h_e; trivial
  | some ei =>
    simp [findEdge] at h_ei
    have : g.vertices[a]? = some (g.vertices[a]) := by simp
    simp [this] at h_ei; rw [Array.findIdx?_eq_some_iff_findIdx_eq] at h_ei
    have : b = g.vertices[a].adj[ei].v := by grind
    rw [this]
    apply EdgeRel.mk a ei

end Graph
