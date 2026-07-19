# garfield

Graph theory in Lean. This is a personal project where I formalize some
theorems in graph theory. Currently, you shouldn't depend on this library yet.

Garfield sounds like graph + lean.

## Scope

- Both directed and undirected graphs
- Both multigraphs and simple graphs
- Unweighted graphs for now, weighted graphs in the future
- Finite graphs only -- no infinite graphs
- Graph classes, following graphclasses.org
- Relationships between the classes
- No proofs of time or memory complexity and therefore
- No efficient algorithms

## Status

The type `Graph (α : Type) : Type` defines unweighted directed graph that allows loops and multiple edges.

- [x] Walk/Reachability
- [ ] Connected components
- [ ] Paths
- [ ] Shortest paths
- [x] Bipartiteness
- [ ] Trees and forests
- [ ] Rooted trees and encoding them into an inductive type
- [ ] Subgraphs and induced subgraphs
- [ ] Spanning trees

### Most important theorems proven

- Every cycle in a bipartite graph has an even length (`isBipartite_walk_parity`).

