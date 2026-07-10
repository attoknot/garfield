import Garfield

open Graph

@[simp]
def g : Graph Unit Unit :=
  let (g, v0) := Graph.empty.addVertex ()
  let (g, v1) := g.addVertex ()
  let (g, v2) := g.addVertex ()
  g |>.addEdge v0 v1 ()
    |>.addEdge v1 v2 ()
    |>.addEdge v1 v0 ()

@[grind =]
theorem g_vertices_size : g.vertices.size = 3 := rfl

#eval g.vertices
#eval (findEdgeRel g 0 1 (by grind) (by simp [Graph.empty, Graph.addVertex, findEdge]; rfl))
#eval (findEdgeRel g 1 0 (by grind))
#eval (findEdgeRel g 1 2 (by grind))

def edge01 : g.EdgeRel 0 1 := match findEdgeRel g 0 1 (h_a := by grind) with
  | some x => x
  | none => unreachable!
  
  

#eval (Walk.step (g.findEdgeRel 0 1 _ _) g.findEdgeRel 0 1 : g.Walk 0 0)

def main : IO Unit :=
  IO.println s!"Hello, world!"
