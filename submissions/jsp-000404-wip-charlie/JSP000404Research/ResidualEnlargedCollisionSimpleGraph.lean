import JSP000404Research.ResidualEnlargedLossDegree
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Finite
import Mathlib.Tactic

/-!
# Collision graph of an enlarged minimal Hall core

The vertices are the members of a finite core T. Two distinct vertices are
adjacent exactly when their enlarged candidate blocks intersect.

This packages the set-theoretic collision relation into Mathlib's SimpleGraph
API so that connectedness, acyclicity, trees, leaves, and cycles can be used
directly.
-/

namespace JSP000404Research
namespace OrderedEdgeColoring

theorem enlargedBlocksCross_symm
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    {u v : V} :
    EnlargedBlocksCross C exponent u v ↔
      EnlargedBlocksCross C exponent v u := by
  unfold EnlargedBlocksCross
  simpa [Finset.inter_comm]

noncomputable def enlargedCollisionGraph
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (T : Finset V) :
    SimpleGraph {v : V // v ∈ T} :=
  SimpleGraph.fromRel fun u v =>
    EnlargedBlocksCross C exponent u.1 v.1

@[simp] theorem enlargedCollisionGraph_adj
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (T : Finset V)
    (u v : {x : V // x ∈ T}) :
    (enlargedCollisionGraph C exponent T).Adj u v ↔
      u ≠ v ∧ EnlargedBlocksCross C exponent u.1 v.1 := by
  classical
  simp [enlargedCollisionGraph, enlargedBlocksCross_symm C exponent]

theorem enlargedCollisionGraph_adj_of_cross
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (T : Finset V)
    {u v : V}
    (hu : u ∈ T)
    (hv : v ∈ T)
    (huv : u ≠ v)
    (hcross : EnlargedBlocksCross C exponent u v) :
    (enlargedCollisionGraph C exponent T).Adj
      ⟨u,hu⟩ ⟨v,hv⟩ := by
  exact (enlargedCollisionGraph_adj
    C exponent T ⟨u,hu⟩ ⟨v,hv⟩).2
    ⟨by
      intro h
      exact huv (congrArg Subtype.val h),
     hcross⟩

theorem enlargedCollisionGraph_cross_of_adj
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (T : Finset V)
    {u v : {x : V // x ∈ T}}
    (h : (enlargedCollisionGraph C exponent T).Adj u v) :
    EnlargedBlocksCross C exponent u.1 v.1 :=
  (enlargedCollisionGraph_adj C exponent T u v).1 h |>.2

#print axioms enlargedCollisionGraph_adj

end OrderedEdgeColoring
end JSP000404Research
