import Garfield.Basic
import Cslib.Algorithms.Lean.TimeM
open Cslib.Algorithms.Lean

variable {α β : Type} (g : Graph α β)

def validColors (colors : Array Bool) : Bool :=
  colors.size == g.vertexCount &&
  (List.range g.vertexCount).all (fun a =>
    match g.vertices[a]? with
    | none => false
    | some av =>
        av.adj.all (fun e =>
          colors[a]? != colors[e.v]?))


def f : TimeM ℕ (Array Bool) := 
  let action : StateT (Array Bool) (TimeM ℕ) (Array Bool) := do
    pure #[]
  StateT.run' action (Array.replicate 10 false)


  
  

