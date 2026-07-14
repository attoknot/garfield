import Garfield.Basic
import Cslib.Algorithms.Lean.TimeM
open Cslib.Algorithms.Lean

variable {α β : Type} (g : Graph α β)

def Connected : Prop :=
  ∀ i j, (h_i : i < g.vertices.size) → (h_j : j < g.vertices.size) →
  ∃ w : Walk, w.start = i ∧ w.end' = j

def decideConnected : Bool :=
  sorry

