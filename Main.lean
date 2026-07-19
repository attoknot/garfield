import Garfield


section

def g : Graph (Fin 2) := Graph.empty.addVertex.addVertex
  |>.addEdge 1 0
  |>.addEdge 0 1

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

def main : IO Unit :=
  IO.println s!"Hello, world!"
