import Garfield.Basic
import Cslib.Algorithms.Lean.TimeM
open Cslib.Algorithms.Lean

example a (xs ys : Array ℕ) :
  (∀ x, x ∈ xs → x ∈ ys) →
  (∀ x, x ∈ xs.erase a → x ∈ ys.erase a) := by grind
variable {α β : Type} [Inhabited α] [BEq β] (g : Graph α β)

@[simp]
def Reachable (a b : ℕ) : Prop := ∃ w, Walk.valid w g ∧ w.start = a ∧ w.end' = b

def ReachableSet (a : ℕ) (reachable : Array ℕ) :=
  ∀ i, (h_i : i < g.vertices.size) →
    Reachable g a i ↔ i ∈ reachable

inductive Topsort' : Array ℕ → Prop
| nil : Topsort' #[]
| cons a xs rset :
    ReachableSet g a rset →
    (∀ x, x ∈ rset → x ∈ xs) →
    Topsort' (Array.push xs a)

def Topsort (ts : Array ℕ) : Prop := ts.size = g.vertices.size ∧ Topsort' g ts

def decideReachableSet' (unvisited : Array ℕ) (a : ℕ) : Array ℕ :=
  match h_in : unvisited.contains a with
  | false => #[]
  | true =>
      g.vertices[a]!.adj.flatMap (fun b =>
        have : (unvisited.erase a).size < unvisited.size := by grind
        decideReachableSet' (unvisited.erase a) b.v)
      |>.push a
termination_by unvisited.size

def decideReachableSet (a : ℕ) : Array ℕ := decideReachableSet' g (Array.range g.vertices.size) a

def decideReachableSet'_sound unvisited a b
    (h_a : a < g.vertices.size)
    (h : b ∈ decideReachableSet' g unvisited a) :
    Reachable g a b := by
  induction unvisited, a using decideReachableSet'.induct
  case case1 unvisited a h_in =>
    unfold decideReachableSet' at h
    rw! [h_in] at h; simp at h
  case case2 x unvisited a h_in ih =>
    unfold decideReachableSet' at h
    rw! [h_in] at h; simp at h
    have h_e : (∃ e, e ∈ g.vertices[a]!.adj ∧ b ∈ decideReachableSet' g (unvisited.erase a) e.v) ∨ b = a := h
    cases h_e
    case inr a_eq_b =>
      rw [a_eq_b]
      refine ⟨ Walk.refl a, ?_, rfl, rfl ⟩
      show Walk.refl a |>.valid g
      sorry
    case inl h_e =>
      rcases h_e with ⟨ e, h_e_in, h_b_in ⟩
      have r_ev_b : Reachable g e.v b := ih e (by sorry) h_b_in  -- needs the validity of the graph
      rcases r_ev_b with ⟨ w_ev_b, h_ev_b ⟩
      have r_a_ev : Reachable g a e.v := by
        rcases Array.mem_iff_getElem?.mp h_e_in with ⟨ ei, h_ei ⟩
        have h_ei : g.vertices[a].adj[ei]? = some e := by grind
        refine ⟨ Walk.leg a e.v ei, ?_, by tauto ⟩
        have : (Walk.leg a e.v ei).getVertices g = #[some a, some e.v] := by
          dsimp [Walk.leg, Walk.getVertices]
          rw! [Array.scanl_singleton]
          simp [h_a, h_ei]
        simp [Walk.valid]; constructor
        · rw! [this]
          rintro ⟨ _ | ⟨ _ | i ⟩ ⟩  h_i <;> simp
          · assumption
          · show e.v < g.vertices.size
            -- after we add validity of graphs, it can be obtained from there
            -- currently, it can still be obtained through h_ev_b but it is too difficult
            rcases h_ev_b with ⟨ h_ev_b, h_ev_b_start, _ ⟩
            simp [Walk.valid] at h_ev_b
            have := h_ev_b.1 0 (by grind)
            simp [Walk.getVertices] at this
            rw [h_ev_b_start] at this
            exact this
        · rw! [this]
          simp [Walk.leg]

      rcases r_a_ev with ⟨ w_a_ev, h_a_ev ⟩
      refine ⟨ Walk.trans w_a_ev w_ev_b, ?_, by tauto ⟩
      show Walk.trans _ _ |>.valid g
      sorry

def decideReachableSet'_weaken unvis0 unvis1 a
    (h : ∀ x, x ∈ unvis0 → x ∈ unvis1) :
    unvis0.toList.Nodup → unvis1.toList.Nodup →
    ∀ x, x ∈ decideReachableSet' g unvis0 a → x ∈ decideReachableSet' g unvis1 a := by
  revert unvis1
  induction unvis0, a using decideReachableSet'.induct
  case case1 unvis0 a h_in =>
    unfold decideReachableSet'; rw! [h_in]; simp
  case case2 unvisited a h_in ih =>
    intros unvis1 h nodup nodup1
    unfold decideReachableSet'
    have h_in1 : unvis1.contains a := by grind
    rw! [h_in, h_in1]; simp
    rintro b h_e
    cases h_e
    case inr b_eq_a =>
      right; trivial
    case inl h =>
      rcases h with ⟨ e, h_e_in, h_b_in ⟩
      left
      use e, h_e_in
      apply ih
      · intro x x_in_unvis
        have := h x
        grind [Array.mem_def]
      · grind
      · grind
      · assumption

#check decideReachableSet'.induct

def decideReachableSet'_complete a b :
    Reachable g a b → ∃ unvis, b ∈ decideReachableSet' g unvis a := by
  rintro ⟨ w_ab, h_ab ⟩
  


