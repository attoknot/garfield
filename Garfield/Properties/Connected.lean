import Garfield.Basic
import Cslib.Algorithms.Lean.TimeM
open Cslib.Algorithms.Lean

variable {α β : Type} (g : Graph α β)

def Connected : Prop :=
  g.vertices.All
