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


theorem minimal_enlargedCollisionGraph_preconnected
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    {T : Finset V}
    (hdef :
      BlockDeficient
        (fun x => 2 ^ exponent x)
        (enlargedProjectedCandidateBlock C exponent)
        T)
    (hmin :
      ∀ U : Finset V,
        U ⊂ T →
        ¬ BlockDeficient
          (fun x => 2 ^ exponent x)
          (enlargedProjectedCandidateBlock C exponent)
          U) :
    (enlargedCollisionGraph C exponent T).Preconnected := by
  classical
  let G := enlargedCollisionGraph C exponent T
  intro u v
  by_contra huvReach

  let A : Finset V :=
    T.filter fun x =>
      ∃ hx : x ∈ T, G.Reachable u ⟨x,hx⟩
  let B : Finset V := T \ A

  have hAsub : A ⊆ T := by
    intro x hx
    exact (Finset.mem_filter.mp hx).1

  have hA : A.Nonempty := by
    refine ⟨u.1,?_⟩
    apply Finset.mem_filter.mpr
    refine ⟨u.2,?_⟩
    exact ⟨u.2, SimpleGraph.Reachable.refl⟩

  have hvNotA : v.1 ∉ A := by
    intro hvA
    obtain ⟨_hvT,hvReach⟩ :=
      Finset.mem_filter.mp hvA
    obtain ⟨hvProof,hReach⟩ := hvReach
    apply huvReach
    simpa using hReach

  have hB : B.Nonempty := by
    refine ⟨v.1,?_⟩
    exact Finset.mem_sdiff.mpr ⟨v.2,hvNotA⟩

  have hdisjAB : Disjoint A B := by
    exact Finset.disjoint_sdiff_right

  have hunion : A ∪ B = T := by
    dsimp [B]
    exact Finset.union_sdiff_of_subset hAsub

  have hcross :
      Disjoint
        (A.biUnion
          (enlargedProjectedCandidateBlock C exponent))
        (B.biUnion
          (enlargedProjectedCandidateBlock C exponent)) := by
    rw [Finset.disjoint_left]
    intro word hwordA hwordB
    obtain ⟨x,hxA,hxWord⟩ :=
      Finset.mem_biUnion.mp hwordA
    obtain ⟨y,hyB,hyWord⟩ :=
      Finset.mem_biUnion.mp hwordB

    have hxT : x ∈ T := hAsub hxA
    have hyData := Finset.mem_sdiff.mp hyB
    have hyT : y ∈ T := hyData.1
    have hyNotA : y ∉ A := hyData.2
    have hxy : x ≠ y := by
      intro h
      subst y
      exact hyNotA hxA

    have hCrossXY :
        EnlargedBlocksCross C exponent x y := by
      exact ⟨word,hxWord,hyWord⟩
    have hAdj :
        G.Adj ⟨x,hxT⟩ ⟨y,hyT⟩ := by
      dsimp [G]
      exact enlargedCollisionGraph_adj_of_cross
        C exponent T hxT hyT hxy hCrossXY

    obtain ⟨_hxT,hxReachData⟩ :=
      Finset.mem_filter.mp hxA
    obtain ⟨hxProof,hxReach⟩ := hxReachData
    have hxReach' :
        G.Reachable u ⟨x,hxT⟩ := by
      simpa using hxReach
    have hyReach :
        G.Reachable u ⟨y,hyT⟩ :=
      hxReach'.trans hAdj.reachable

    have hyA : y ∈ A := by
      apply Finset.mem_filter.mpr
      refine ⟨hyT,?_⟩
      exact ⟨hyT,hyReach⟩
    exact hyNotA hyA

  exact minimal_deficient_no_noncross_partition
    (fun x : V => 2 ^ exponent x)
    (enlargedProjectedCandidateBlock C exponent)
    hdef hmin hA hB hdisjAB hunion hcross

theorem minimal_enlargedCollisionGraph_connected
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    {T : Finset V}
    (hT : T.Nonempty)
    (hdef :
      BlockDeficient
        (fun x => 2 ^ exponent x)
        (enlargedProjectedCandidateBlock C exponent)
        T)
    (hmin :
      ∀ U : Finset V,
        U ⊂ T →
        ¬ BlockDeficient
          (fun x => 2 ^ exponent x)
          (enlargedProjectedCandidateBlock C exponent)
          U) :
    (enlargedCollisionGraph C exponent T).Connected := by
  rw [SimpleGraph.connected_iff]
  constructor
  · exact minimal_enlargedCollisionGraph_preconnected
      C exponent hdef hmin
  · obtain ⟨v,hv⟩ := hT
    exact ⟨⟨v,hv⟩⟩


theorem enlarged_minimal_deficient_core_card_ge_two
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexpLt : ∀ x, exponent x < n)
    (hexp : ∀ x, exponent x ≤ n)
    (honeLoss :
      ∀ x, (active C x).card ≤ n - exponent x + 1)
    {T : Finset V}
    (hdef :
      BlockDeficient
        (fun x => 2 ^ exponent x)
        (enlargedProjectedCandidateBlock C exponent)
        T) :
    2 ≤ T.card := by
  classical
  have hT :
      T.Nonempty :=
    deficient_set_nonempty_of_positive_demands
      (fun x : V => 2 ^ exponent x)
      (enlargedProjectedCandidateBlock C exponent)
      (fun x => by positivity)
      hdef
  have hcardPos : 0 < T.card :=
    Finset.card_pos.mpr hT
  by_contra hnot
  have hcardLe : T.card ≤ 1 := by
    omega
  have hcardEq : T.card = 1 := by
    omega
  obtain ⟨v,hTv⟩ := Finset.card_eq_one.mp hcardEq
  subst T
  have hlocal :=
    enlargedProjectedCandidateBlock_local_capacity
      C exponent hexpLt hexp honeLoss v
  unfold BlockDeficient at hdef
  simp at hdef
  omega

theorem minimal_enlargedCollisionGraph_two_leaves_of_acyclic
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexpLt : ∀ x, exponent x < n)
    (hexp : ∀ x, exponent x ≤ n)
    (honeLoss :
      ∀ x, (active C x).card ≤ n - exponent x + 1)
    {T : Finset V}
    (hdef :
      BlockDeficient
        (fun x => 2 ^ exponent x)
        (enlargedProjectedCandidateBlock C exponent)
        T)
    (hmin :
      ∀ U : Finset V,
        U ⊂ T →
        ¬ BlockDeficient
          (fun x => 2 ^ exponent x)
          (enlargedProjectedCandidateBlock C exponent)
          U)
    (hacyclic :
      (enlargedCollisionGraph C exponent T).IsAcyclic) :
    ∃ u v : {x : V // x ∈ T},
      u ≠ v ∧
      (enlargedCollisionGraph C exponent T).degree u = 1 ∧
      (enlargedCollisionGraph C exponent T).degree v = 1 := by
  classical
  let G := enlargedCollisionGraph C exponent T
  have hT :
      T.Nonempty :=
    deficient_set_nonempty_of_positive_demands
      (fun x : V => 2 ^ exponent x)
      (enlargedProjectedCandidateBlock C exponent)
      (fun x => by positivity)
      hdef
  have hconn :
      G.Connected := by
    dsimp [G]
    exact minimal_enlargedCollisionGraph_connected
      C exponent hT hdef hmin
  have hcard :
      2 ≤ T.card :=
    enlarged_minimal_deficient_core_card_ge_two
      C exponent hexpLt hexp honeLoss hdef
  have hcardSubtype :
      1 < Fintype.card {x : V // x ∈ T} := by
    simpa using hcard
  letI : Nontrivial {x : V // x ∈ T} :=
    Fintype.one_lt_card_iff_nontrivial.mp hcardSubtype
  have htree : G.IsTree := by
    exact ⟨hconn,hacyclic⟩
  exact htree.exists_ne_and_degree_eq_one

#print axioms enlargedCollisionGraph_adj
#print axioms minimal_enlargedCollisionGraph_preconnected
#print axioms minimal_enlargedCollisionGraph_connected
#print axioms enlarged_minimal_deficient_core_card_ge_two
#print axioms minimal_enlargedCollisionGraph_two_leaves_of_acyclic

end OrderedEdgeColoring
end JSP000404Research
