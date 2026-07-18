import Mathlib.Logic.Relation
import Batteries.Data.Array.Scan
import Mathlib.Order.Defs.LinearOrder
import Mathlib.Order.Fin.Basic
import Mathlib.Algebra.Group.Even
import Mathlib.Algebra.Group.Nat.Even
import Mathlib.Data.Fintype.Basic
import Mathlib.GroupTheory.Perm.Basic

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

instance{n} : Repr (Graph (Fin n)) where
  reprPrec := reprPrec ∘ Graph.toList

-- todo: remove simp in the future
@[simp]
def Graph.empty : Graph (Fin 0) where
  edges a b := by cases a; contradiction

@[simp]
def Graph.singleton : Graph (Fin 1) where
  edges _ _ := 0

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

@[simp]
def Graph.addSymmEdge {n : ℕ} (g : Graph (Fin n)) (a b : Fin n) : Graph (Fin n) where
  edges a' b' :=
    if (a = a' ∧ b = b') ∨ (a = b' ∧ b = a')
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

def prepend {a b c : α} (x : Edge g a b) (w : Walk g b c) : Walk g a c :=
  match w with
  | .nil => Walk.cons Walk.nil x
  | .cons w edge => Walk.cons (prepend x w) edge

def concat {a b c : α} (w0 : Walk g a b) (w1 : Walk g b c) : Walk g a c :=
  match w1 with
  | .nil => w0
  | .cons w1 edge => Walk.cons (concat w0 w1) edge

end Walk

@[ext]
structure Path {α} (g : Graph α) (a b : α) where
  walk : Walk g a b
  is_path : walk.isPath

namespace Graph

variable {α : Type} (g : Graph α)

-- simple classes

def isLoopless : Prop :=
  ∀ a : α, g.edges a a = 0

def isMultiless : Prop :=
  ∀ a b : α, g.edges a b ≤ 1

def isSimple : Prop :=
  g.isLoopless ∧ g.isMultiless

def isUndirected : Prop :=
  ∀ a b : α, g.edges a b = g.edges b a

@[simp, grind]
def Reachable (a b : α) : Prop := Nonempty (Walk g a b)

def isConnected : Prop := ∀ a b : α, Reachable g a b

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
    Walk.prepend edge' (reverse_walk (h_undirected := h_undirected) w)

theorem isConnected_of_isUndirected [LinearOrder α]
    (h_undirected : g.isUndirected)
    (h : (∀ a b : α, a < b → Reachable g a b)) :
    g.isConnected := by
  intros a b
  rcases lt_trichotomy a b with a_lt_b | a_eq_b | a_gt_b
  · apply h; assumption
  · rw [a_eq_b]
    use Walk.nil
  · rcases h b a (by lia) with ⟨ walk ⟩
    use reverse_walk g (h_undirected := h_undirected) walk

def isDirectedAcyclic : Prop := ∀ (a : α) (w : Walk g a a), !w.isCycle

def isUndirectedAcyclic : Prop := ∀ (a b : α), Path g a b → Edge g b a → False

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

def isTree : Prop := g.isSimple ∧ g.isUndirected ∧ g.isUndirectedAcyclic ∧ g.isConnected

/- only makes sense with undirected graphs -/
def Leaf (leaf neighbor : α) := ∀ a : α, a ≠ leaf → a ≠ neighbor → g.edges leaf a = 0

end Graph

def Graph.removeLeaf {n} (g : Graph (Fin n)) (leaf : Fin n) : Graph (Fin (n - 1)) where
  edges a b := match a, b with
    | ⟨a, ha⟩, ⟨b, hb⟩ =>
      if h : a < leaf ∨ b < leaf
      then g.edges ⟨a, by lia⟩ ⟨b, by lia⟩
      else g.edges ⟨a + 1, by lia⟩ ⟨b + 1, by lia⟩

def Graph.addLeaf {n} (g : Graph (Fin n)) (neighbor : Fin n) : Graph (Fin (n + 1)) where
  edges a b := match a, b with
    | ⟨a, ha⟩, ⟨b, hb⟩ =>
      if h : a = n ∨ b = n
      then if h2 : a = neighbor ∨ b = neighbor then 1 else 0
      else g.edges ⟨a, by lia⟩ ⟨b, by lia⟩

def walk_of_addLeaf {n} (g : Graph (Fin n)) neighbor (a b : Fin n) (w : Walk g a b) :
    Walk (g.addLeaf neighbor) ⟨a, by lia⟩ ⟨b, by lia⟩ :=
  match w with
  | .nil => Walk.nil
  | .cons (b := b) (c := c) w edge =>
    Walk.cons (walk_of_addLeaf g neighbor (w := w))
      ⟨edge.val, by simp [Graph.addLeaf]; lia⟩

theorem Graph.isTree_of_singleton :
    Graph.singleton.isTree := by
  simp [Graph.isTree, Graph.isSimple, Graph.isLoopless, Graph.isMultiless, Graph.isUndirected, Graph.isUndirectedAcyclic, Graph.isConnected]
  constructor
  · rintro ⟨_, _⟩ ⟨_, _⟩; grind
  · use Walk.nil

theorem Graph.isTree_of_addLeaf {n} (g : Graph (Fin n)) neighbor :
    g.isTree → (g.addLeaf neighbor).isTree := by
  dsimp [Graph.isTree]
  intros h_istree
  have h_undirected : (g.addLeaf neighbor).isUndirected := by
    simp [Graph.addLeaf, Graph.isUndirected] at ⊢ h_istree; grind
  refine ⟨ ⟨ ?_, ?_⟩, h_undirected, ?_, ?_⟩
  · simp [Graph.addLeaf, Graph.isSimple, Graph.isLoopless] at ⊢ h_istree; grind
  · simp [Graph.addLeaf, Graph.isSimple, Graph.isMultiless] at ⊢ h_istree; grind
  · simp [Graph.isUndirectedAcyclic] at ⊢ h_istree
    -- i have no tools for proving acyclicity yet
    sorry
  · apply isConnected_of_isUndirected _ h_undirected
    simp [Graph.isConnected] at ⊢ h_istree
    have h_connected : ∀ (a b : Fin n), Nonempty (Walk g a b) := by tauto
    intros a b a_le_b
    by_cases! h : b < n
    · rcases h_connected ⟨a, by lia⟩ ⟨b, by lia⟩ with ⟨walk⟩
      use walk_of_addLeaf (w := walk) ..
    have b_eq_n : b = n := by lia
    have edge : Edge (g.addLeaf neighbor) ⟨neighbor, by lia⟩ b := ⟨0, by grind [Graph.addLeaf]⟩
    rcases h_connected ⟨a, by lia⟩ neighbor with ⟨walk⟩
    use Walk.cons (walk_of_addLeaf g neighbor (w := walk)) edge

def Graph.shuffle {α β} (g : Graph α) (ρ : Equiv α β) : Graph β where
  edges a b := g.edges (ρ.symm a) (ρ.symm b)

-- very useless

def Graph.union {n m : ℕ} (ga : Graph (Fin n)) (gb : Graph (Fin m)) : Graph (Fin (n + m)) where
  edges a b := match a, b with
    | ⟨a, ha⟩, ⟨b, hb⟩ =>
      if h : a < n ∧ b < n then ga.edges ⟨a, by lia⟩ ⟨b, by lia⟩ else
      if h : a ≥ n ∧ b ≥ n then gb.edges ⟨a - n, by lia⟩ ⟨b - n, by lia⟩ else
      0

def Graph.split {n ma mb : ℕ} {h : n = ma + mb} (g : Graph (Fin n)) : (Graph (Fin ma)) × (Graph (Fin mb)) :=
  ⟨
  { edges a b := match a, b with
    | ⟨a, ha⟩, ⟨b, hb⟩ => g.edges ⟨a, by lia⟩ ⟨b, by lia⟩
  },
  { edges a b := match a, b with
    | ⟨a, ha⟩, ⟨b, hb⟩ => g.edges ⟨ma + a, by lia⟩ ⟨ma + b, by lia⟩
  } ⟩

theorem Graph.split_union {n m : ℕ} (ga : Graph (Fin n)) (gb : Graph (Fin m)) :
    ⟨ga, gb⟩ = Graph.split (h := by grind) (Graph.union ga gb) := by
  ext <;> simp [Graph.split, Graph.union]
  grind

theorem Graph.union_split {n ma mb : ℕ} {h : n = ma + mb} (g : Graph (Fin n))
    (h_no_intersection : ∀ a b h1 h2, ¬(a < ma ↔ b < ma) → g.edges ⟨a, h1⟩ ⟨b, h2⟩ = 0) :
    g =
      let (a, b) := Graph.split (h := h) (ma := ma) (mb := mb) g
      by rw [h]; exact Graph.union a b := by
  cases g with | mk edges =>
  subst h; simp [Graph.split, Graph.union]
  grind

def Graph.connectUnion {na nb : ℕ} (ga : Graph (Fin na)) (gb : Graph (Fin nb)) (a : Fin na) (b : Fin nb) : Graph (Fin (na + nb)) :=
  ga.union gb |>.addSymmEdge ⟨a, by lia⟩ ⟨na + b, by lia⟩

theorem Graph.isUndirected_of_connectUnion{na nb : ℕ} (ga : Graph (Fin na)) (gb : Graph (Fin nb)) a b:
    ga.isUndirected → gb.isUndirected →
    Graph.isUndirected (Graph.connectUnion ga gb a b) := by
  simp [Graph.isUndirected, Graph.connectUnion, Graph.union]
  grind

def Graph.walk_of_union_l {na nb : ℕ} (ga : Graph (Fin na)) (gb : Graph (Fin nb)) {a b}
    (w : Walk ga a b) :
    Walk (ga.union gb) ⟨a, by lia⟩ ⟨b, by lia⟩ :=
  match w with
  | .nil => Walk.nil
  | .cons w edge => Walk.cons (Graph.walk_of_union_l ga gb w) ⟨edge.1, by simp [Graph.union]⟩

def Graph.walk_of_union_r {na nb : ℕ} (ga : Graph (Fin na)) (gb : Graph (Fin nb)) {a b}
    (w : Walk gb a b) :
    Walk (ga.union gb) ⟨na + a, by lia⟩ ⟨na + b, by lia⟩ :=
  match w with
  | .nil => Walk.nil
  | .cons w edge => Walk.cons (Graph.walk_of_union_r ga gb w) ⟨edge.1, by grind [Graph.union]⟩

def Graph.walk_of_addSymmEdge {n : ℕ} (g : Graph (Fin n)) {a b} {va vb}
    (w : Walk g a b) :
    Walk (g.addSymmEdge va vb) a b :=
  match w with
  | .nil => Walk.nil
  | .cons w edge => Walk.cons (Graph.walk_of_addSymmEdge g w) ⟨edge.1, by grind [Graph.addSymmEdge]⟩

def Graph.walk_of_connectUnion_l {na nb : ℕ} (ga : Graph (Fin na)) (gb : Graph (Fin nb)) {a b} {va vb}
    (w : Walk ga a b) :
    Walk (Graph.connectUnion ga gb va vb) ⟨a, by lia⟩ ⟨b, by lia⟩ := by
  dsimp only [Graph.connectUnion]
  apply walk_of_addSymmEdge
  apply walk_of_union_l
  exact w

def Graph.walk_of_connectUnion_r {na nb : ℕ} (ga : Graph (Fin na)) (gb : Graph (Fin nb)) {a b} {va vb}
    (w : Walk gb a b) :
    Walk (Graph.connectUnion ga gb va vb) ⟨na + a, by lia⟩ ⟨na + b, by lia⟩ := by
  dsimp only [Graph.connectUnion]
  apply walk_of_addSymmEdge
  apply walk_of_union_r
  exact w

theorem Graph.isConnected_of_connectUnion {na nb : ℕ} (ga : Graph (Fin na)) (gb : Graph (Fin nb)) a b:
    ga.isUndirected → ga.isConnected →
    gb.isUndirected → gb.isConnected →
    Graph.isConnected (Graph.connectUnion ga gb a b) := by
  simp [Graph.isUndirected, Graph.isConnected]
  intros ga_undirected ga_connected gb_undirected gb_connected
  apply isConnected_of_isUndirected
  · apply isUndirected_of_connectUnion <;> assumption
  intros c d c_le_d; dsimp [Graph.Reachable]
  have : Walk (Graph.connectUnion ga gb a b) ⟨a, by lia⟩ ⟨na + b, by lia⟩ :=
    Walk.cons Walk.nil ⟨0, by simp [Graph.connectUnion]⟩

  by_cases d < na
  · let c : Fin na := ⟨c, by lia⟩
    let d : Fin na := ⟨d, by lia⟩
    show Nonempty (Walk (ga.connectUnion gb a b) ⟨c, _⟩ ⟨d, _⟩)
    rcases ga_connected c d with ⟨walk_c_d⟩
    use (walk_of_connectUnion_l (w := walk_c_d) ..)
  by_cases na ≤ c
  · let c : Fin nb := ⟨c - na, by lia⟩
    let d : Fin nb := ⟨d - na, by lia⟩
    suffices Nonempty (Walk (ga.connectUnion gb a b) ⟨na + c, by lia⟩ ⟨na + d, by lia⟩) by grind
    rcases gb_connected c d with ⟨walk_c_d⟩
    use (walk_of_connectUnion_r (w := walk_c_d) ..)
  · let c : Fin na := ⟨c, by lia⟩
    let d : Fin nb := ⟨d - na, by lia⟩
    suffices Nonempty (Walk (ga.connectUnion gb a b) ⟨c, by lia⟩ ⟨na + d, by lia⟩) by grind
    rcases ga_connected c a with ⟨walk_c_a⟩
    rcases gb_connected b d with ⟨walk_b_d⟩
    have : Walk (Graph.connectUnion ga gb a b) ⟨a, by lia⟩ ⟨na + b, by lia⟩ :=
      Walk.nil.cons ⟨0, by simp [Graph.connectUnion]⟩
    constructor
    refine Walk.concat (Walk.concat ?_ this) ?_
    · exact walk_of_connectUnion_l (w := walk_c_a) ..
    · exact walk_of_connectUnion_r (w := walk_b_d) ..

theorem Graph.addLeaf_is_connectUnion {n} (g : Graph (Fin n)) neighbor :
    g.addLeaf neighbor = Graph.connectUnion g (Graph.singleton) neighbor 0 := by
  simp [Graph.addLeaf, Graph.connectUnion, Graph.union, Graph.addSymmEdge, Graph.singleton]
  grind

inductive Tree where
| Leaf : Tree
| Node : List Tree → Tree

namespace Tree

def ofGraph {n : ℕ} {h : n > 0} (g : Graph (Fin n)) (visited : Fin n → Bool) : Tree :=
  match n with
  | 0 => by contradiction
  | 1 => Leaf
  | n + 1 => Node <|
    List.range n |>.flatMap fun next =>
      if g.edges ⟨n, sorry⟩ ⟨next, sorry⟩ == 0 then []
      else sorry

end Tree

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
