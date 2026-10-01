import JSP000404Research.ResidualEnlargedLossDegree
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.Girth
import Mathlib.Combinatorics.SimpleGraph.Clique
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


theorem enlargedCollisionGraph_degree_one_unique_neighbor
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (T : Finset V)
    (u : {x : V // x ∈ T})
    (hdeg :
      (enlargedCollisionGraph C exponent T).degree u = 1) :
    ∃ w : V,
      w ∈ T ∧
      w ≠ u.1 ∧
      ∀ z : V,
        z ∈ T →
        z ≠ u.1 →
        EnlargedBlocksCross C exponent u.1 z →
        z = w := by
  classical
  let G := enlargedCollisionGraph C exponent T
  obtain ⟨w, huw, huniq⟩ :=
    SimpleGraph.degree_eq_one_iff_existsUnique_adj.mp hdeg
  refine ⟨w.1,w.2,?_,?_⟩
  · exact (G.ne_of_adj huw).symm
  · intro z hzT hzu hcross
    have huz :
        G.Adj u ⟨z,hzT⟩ := by
      dsimp [G]
      exact enlargedCollisionGraph_adj_of_cross
        C exponent T u.2 hzT
        (by
          intro h
          exact hzu (congrArg Subtype.val h))
        hcross
    have hsubEq : (⟨z,hzT⟩ : {x : V // x ∈ T}) = w :=
      huniq _ huz
    exact congrArg Subtype.val hsubEq

theorem minimal_enlargedCollisionGraph_two_unique_leaves_of_acyclic
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
    ∃ u v wu wv : V,
      u ∈ T ∧
      v ∈ T ∧
      u ≠ v ∧
      wu ∈ T ∧
      wv ∈ T ∧
      wu ≠ u ∧
      wv ≠ v ∧
      (
        ∀ z : V,
          z ∈ T →
          z ≠ u →
          EnlargedBlocksCross C exponent u z →
          z = wu
      ) ∧
      (
        ∀ z : V,
          z ∈ T →
          z ≠ v →
          EnlargedBlocksCross C exponent v z →
          z = wv
      ) := by
  obtain ⟨u,v,huv,hdu,hdv⟩ :=
    minimal_enlargedCollisionGraph_two_leaves_of_acyclic
      C exponent hexpLt hexp honeLoss hdef hmin hacyclic
  obtain ⟨wu,hwuT,hwuNe,huniqU⟩ :=
    enlargedCollisionGraph_degree_one_unique_neighbor
      C exponent T u hdu
  obtain ⟨wv,hwvT,hwvNe,huniqV⟩ :=
    enlargedCollisionGraph_degree_one_unique_neighbor
      C exponent T v hdv
  exact ⟨u.1,v.1,wu,wv,
    u.2,v.2,
    (by
      intro h
      apply huv
      apply Subtype.ext
      exact h),
    hwuT,hwvT,hwuNe,hwvNe,
    huniqU,huniqV⟩


theorem minimal_enlargedCollisionGraph_two_leaf_outlets_of_acyclic
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
    ∃ u v wu wv : V,
      u ∈ T ∧
      v ∈ T ∧
      u ≠ v ∧
      wu ∈ T ∧
      wv ∈ T ∧
      wu ≠ u ∧
      wv ≠ v ∧
      EnlargedLeafOutlet C exponent T u wu ∧
      EnlargedLeafOutlet C exponent T v wv := by
  obtain ⟨u,v,wu,wv,
      huT,hvT,huv,hwuT,hwvT,hwuNe,hwvNe,
      huniqU,huniqV⟩ :=
    minimal_enlargedCollisionGraph_two_unique_leaves_of_acyclic
      C exponent hexpLt hexp honeLoss
      hdef hmin hacyclic
  have huOutlet :=
    minimal_enlargedCandidate_any_leaf_outlet
      C exponent hexpLt hexp honeLoss
      hdef hmin huT huniqU
  have hvOutlet :=
    minimal_enlargedCandidate_any_leaf_outlet
      C exponent hexpLt hexp honeLoss
      hdef hmin hvT huniqV
  exact ⟨u,v,wu,wv,
    huT,hvT,huv,hwuT,hwvT,hwuNe,hwvNe,
    huOutlet,hvOutlet⟩


theorem minimal_enlargedCollisionGraph_cycle_of_not_acyclic
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    {T : Finset V}
    (hcyclic :
      ¬ (enlargedCollisionGraph C exponent T).IsAcyclic) :
    ∃ a : {x : V // x ∈ T},
      ∃ p :
        (enlargedCollisionGraph C exponent T).Walk a a,
        p.IsCycle := by
  let G := enlargedCollisionGraph C exponent T
  have h :=
    (SimpleGraph.exists_girth_eq_length
      (G := G)).2 hcyclic
  obtain ⟨a,p,hcycle,_hgirth⟩ := h
  exact ⟨a,p,hcycle⟩

theorem enlargedCollisionCycle_edge_cross
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (T : Finset V)
    {u v : {x : V // x ∈ T}}
    (hadj :
      (enlargedCollisionGraph C exponent T).Adj u v) :
    EnlargedBlocksCross C exponent u.1 v.1 :=
  enlargedCollisionGraph_cross_of_adj
    C exponent T hadj


theorem minimal_enlargedCollisionGraph_leaf_outlets_or_cycle
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
          U) :
    (
      ∃ u v wu wv : V,
        u ∈ T ∧
        v ∈ T ∧
        u ≠ v ∧
        wu ∈ T ∧
        wv ∈ T ∧
        wu ≠ u ∧
        wv ≠ v ∧
        EnlargedLeafOutlet C exponent T u wu ∧
        EnlargedLeafOutlet C exponent T v wv
    )
    ∨
    (
      ∃ a : {x : V // x ∈ T},
        ∃ p :
          (enlargedCollisionGraph C exponent T).Walk a a,
          p.IsCycle
    ) := by
  by_cases hacyclic :
      (enlargedCollisionGraph C exponent T).IsAcyclic
  · left
    exact
      minimal_enlargedCollisionGraph_two_leaf_outlets_of_acyclic
        C exponent hexpLt hexp honeLoss
        hdef hmin hacyclic
  · right
    exact
      minimal_enlargedCollisionGraph_cycle_of_not_acyclic
        C exponent hacyclic


theorem simpleGraph_no_triangle_of_three_lt_girth
    {X : Type*} [Fintype X]
    (G : SimpleGraph X)
    (hgirth : 3 < G.girth)
    {u v w : X}
    (huv : G.Adj u v)
    (hvw : G.Adj v w) :
    ¬ G.Adj u w := by
  intro huw
  have hclique :
      G.IsNClique 3 ({u,v,w} : Finset X) := by
    exact (SimpleGraph.is3Clique_triple_iff).2
      ⟨huv,huw,hvw⟩
  have hcycle3 :=
    (SimpleGraph.is3Clique_iff_exists_cycle_length_three
      (G := G)).1 ⟨{u,v,w},hclique⟩
  obtain ⟨a,p,hcycle,hp3⟩ := hcycle3
  have hle := hcycle.girth_le_length
  rw [hp3] at hle
  omega

theorem enlargedCollisionGraph_incident_intersections_disjoint_of_three_lt_girth
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (T : Finset V)
    {u v w : {x : V // x ∈ T}}
    (huv :
      (enlargedCollisionGraph C exponent T).Adj u v)
    (hvw :
      (enlargedCollisionGraph C exponent T).Adj v w)
    (huw : u ≠ w)
    (hgirth :
      3 < (enlargedCollisionGraph C exponent T).girth) :
    Disjoint
      (enlargedProjectedCandidateBlock C exponent v.1 ∩
        enlargedProjectedCandidateBlock C exponent u.1)
      (enlargedProjectedCandidateBlock C exponent v.1 ∩
        enlargedProjectedCandidateBlock C exponent w.1) := by
  classical
  rw [Finset.disjoint_left]
  intro word hleft hright
  have hleftParts := Finset.mem_inter.mp hleft
  have hrightParts := Finset.mem_inter.mp hright
  have huwCross :
      EnlargedBlocksCross C exponent u.1 w.1 := by
    exact ⟨word,hleftParts.2,hrightParts.2⟩
  have huwAdj :
      (enlargedCollisionGraph C exponent T).Adj u w := by
    exact enlargedCollisionGraph_adj_of_cross
      C exponent T u.2 w.2
      (by
        intro h
        apply huw
        apply Subtype.ext
        exact h)
      huwCross
  exact
    (simpleGraph_no_triangle_of_three_lt_girth
      (enlargedCollisionGraph C exponent T)
      hgirth huv hvw) huwAdj


theorem enlargedCollisionGraph_triangle_or_three_lt_girth
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (T : Finset V)
    (hcyclic :
      ¬ (enlargedCollisionGraph C exponent T).IsAcyclic) :
    (
      ∃ u v w : {x : V // x ∈ T},
        (enlargedCollisionGraph C exponent T).Adj u v ∧
        (enlargedCollisionGraph C exponent T).Adj u w ∧
        (enlargedCollisionGraph C exponent T).Adj v w
    )
    ∨
    3 < (enlargedCollisionGraph C exponent T).girth := by
  let G := enlargedCollisionGraph C exponent T
  have hthree : 3 ≤ G.girth :=
    SimpleGraph.three_le_girth hcyclic
  by_cases heq : G.girth = 3
  · left
    have hcycleMin :=
      (SimpleGraph.exists_girth_eq_length
        (G := G)).2 hcyclic
    obtain ⟨a,p,hcycle,hgirth⟩ := hcycleMin
    have hp3 : p.length = 3 := by
      omega
    have hcliqueExists :=
      (SimpleGraph.is3Clique_iff_exists_cycle_length_three
        (G := G)).2 ⟨a,p,hcycle,hp3⟩
    obtain ⟨s,hs⟩ := hcliqueExists
    obtain ⟨u,v,w,huv,huw,hvw,_hs⟩ :=
      (SimpleGraph.is3Clique_iff).1 hs
    exact ⟨u,v,w,huv,huw,hvw⟩
  · right
    omega

theorem minimal_enlargedCollisionGraph_leaf_outlets_or_triangle_or_long_cycle
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
          U) :
    (
      ∃ u v wu wv : V,
        u ∈ T ∧
        v ∈ T ∧
        u ≠ v ∧
        wu ∈ T ∧
        wv ∈ T ∧
        wu ≠ u ∧
        wv ≠ v ∧
        EnlargedLeafOutlet C exponent T u wu ∧
        EnlargedLeafOutlet C exponent T v wv
    )
    ∨
    (
      ∃ u v w : {x : V // x ∈ T},
        (enlargedCollisionGraph C exponent T).Adj u v ∧
        (enlargedCollisionGraph C exponent T).Adj u w ∧
        (enlargedCollisionGraph C exponent T).Adj v w
    )
    ∨
    3 < (enlargedCollisionGraph C exponent T).girth := by
  by_cases hacyclic :
      (enlargedCollisionGraph C exponent T).IsAcyclic
  · exact Or.inl
      (minimal_enlargedCollisionGraph_two_leaf_outlets_of_acyclic
        C exponent hexpLt hexp honeLoss
        hdef hmin hacyclic)
  · rcases
      enlargedCollisionGraph_triangle_or_three_lt_girth
        C exponent T hacyclic
      with htri | hlong
    · exact Or.inr (Or.inl htri)
    · exact Or.inr (Or.inr hlong)


noncomputable def coreEnlargedCandidateFibre
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (T : Finset V)
    (word : Fin n → Bool) : Finset V := by
  classical
  exact T.filter fun v =>
    word ∈ enlargedProjectedCandidateBlock C exponent v

@[simp] theorem mem_coreEnlargedCandidateFibre
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (T : Finset V)
    (word : Fin n → Bool)
    (v : V) :
    v ∈ coreEnlargedCandidateFibre C exponent T word ↔
      v ∈ T ∧
      word ∈ enlargedProjectedCandidateBlock C exponent v := by
  classical
  simp [coreEnlargedCandidateFibre]

theorem coreEnlargedCandidateFibre_card_le_two_of_three_lt_girth
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (T : Finset V)
    (hgirth :
      3 < (enlargedCollisionGraph C exponent T).girth)
    (word : Fin n → Bool) :
    (coreEnlargedCandidateFibre C exponent T word).card ≤ 2 := by
  classical
  by_contra hnot
  have hthree :
      3 ≤ (coreEnlargedCandidateFibre
        C exponent T word).card := by
    omega
  obtain ⟨s,hsSub,hsCard⟩ :=
    Finset.exists_subset_card_eq hthree
  have hsCard' : s.card = 3 := hsCard
  obtain ⟨u,v,w,huv,huw,hvw,hsEq⟩ :=
    Finset.card_eq_three.mp hsCard'
  subst s

  have huF :
      u ∈ coreEnlargedCandidateFibre
        C exponent T word :=
    hsSub (by simp)
  have hvF :
      v ∈ coreEnlargedCandidateFibre
        C exponent T word :=
    hsSub (by simp)
  have hwF :
      w ∈ coreEnlargedCandidateFibre
        C exponent T word :=
    hsSub (by simp)

  have huData :=
    (mem_coreEnlargedCandidateFibre
      C exponent T word u).1 huF
  have hvData :=
    (mem_coreEnlargedCandidateFibre
      C exponent T word v).1 hvF
  have hwData :=
    (mem_coreEnlargedCandidateFibre
      C exponent T word w).1 hwF

  let U : {x : V // x ∈ T} := ⟨u,huData.1⟩
  let Vv : {x : V // x ∈ T} := ⟨v,hvData.1⟩
  let W : {x : V // x ∈ T} := ⟨w,hwData.1⟩

  have hUV :
      (enlargedCollisionGraph C exponent T).Adj U Vv := by
    apply enlargedCollisionGraph_adj_of_cross
      C exponent T huData.1 hvData.1 huv
    exact ⟨word,huData.2,hvData.2⟩
  have hVW :
      (enlargedCollisionGraph C exponent T).Adj Vv W := by
    apply enlargedCollisionGraph_adj_of_cross
      C exponent T hvData.1 hwData.1 hvw
    exact ⟨word,hvData.2,hwData.2⟩
  have hUW :
      (enlargedCollisionGraph C exponent T).Adj U W := by
    apply enlargedCollisionGraph_adj_of_cross
      C exponent T huData.1 hwData.1 huw
    exact ⟨word,huData.2,hwData.2⟩

  exact
    (simpleGraph_no_triangle_of_three_lt_girth
      (enlargedCollisionGraph C exponent T)
      hgirth hUV hVW) hUW

#print axioms coreEnlargedCandidateFibre_card_le_two_of_three_lt_girth

end OrderedEdgeColoring
end JSP000404Research
