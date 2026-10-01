import JSP000404Research.ResidualEnlargedLossDegree
import JSP000404Research.ResidualLossTwoExitRecursiveOutlet
import JSP000404Research.ResidualCompletionMultiplicity
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



theorem enlargedCollisionGraph_triangle_has_loss
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (T : Finset V)
    {u v w : {x : V // x ∈ T}}
    (huv :
      (enlargedCollisionGraph C exponent T).Adj u v)
    (huw :
      (enlargedCollisionGraph C exponent T).Adj u w)
    (hvw :
      (enlargedCollisionGraph C exponent T).Adj v w) :
    u.1 ∈ projectedLossVertices C exponent
    ∨ v.1 ∈ projectedLossVertices C exponent
    ∨ w.1 ∈ projectedLossVertices C exponent := by
  classical
  by_contra hnone
  push_neg at hnone
  have huNonloss :
      u.1 ∉ projectedLossVertices C exponent := hnone.1
  have hvNonloss :
      v.1 ∉ projectedLossVertices C exponent := hnone.2.1
  have hwNonloss :
      w.1 ∉ projectedLossVertices C exponent := hnone.2.2

  have huvCross :=
    enlargedCollisionGraph_cross_of_adj
      C exponent T huv
  have huwCross :=
    enlargedCollisionGraph_cross_of_adj
      C exponent T huw
  have hvwCross :=
    enlargedCollisionGraph_cross_of_adj
      C exponent T hvw
  obtain ⟨wordUV,huUV,hvUV⟩ := huvCross
  obtain ⟨wordUW,huUW,hwUW⟩ := huwCross
  obtain ⟨wordVW,hvVW,hwVW⟩ := hvwCross

  rw [enlargedProjectedCandidateBlock_nonloss
        C exponent huNonloss] at huUV huUW
  rw [enlargedProjectedCandidateBlock_nonloss
        C exponent hvNonloss] at hvUV hvVW
  rw [enlargedProjectedCandidateBlock_nonloss
        C exponent hwNonloss] at hwUW hwVW

  have hUV :
      (retainedCompletionWords C u.1 ∩
        retainedCompletionWords C v.1).Nonempty :=
    ⟨wordUV,Finset.mem_inter.mpr ⟨huUV,hvUV⟩⟩
  have hUW :
      (retainedCompletionWords C u.1 ∩
        retainedCompletionWords C w.1).Nonempty :=
    ⟨wordUW,Finset.mem_inter.mpr ⟨huUW,hwUW⟩⟩
  have hVW :
      (retainedCompletionWords C v.1 ∩
        retainedCompletionWords C w.1).Nonempty :=
    ⟨wordVW,Finset.mem_inter.mpr ⟨hvVW,hwVW⟩⟩

  obtain ⟨word,hwordU,hwordV,hwordW⟩ :=
    three_retainedCompletion_pairwise_nonempty_common
      C hUV hUW hVW

  have huvNe : u.1 ≠ v.1 := by
    intro h
    apply (enlargedCollisionGraph C exponent T).ne_of_adj huv
    apply Subtype.ext
    exact h
  have huwNe : u.1 ≠ w.1 := by
    intro h
    apply (enlargedCollisionGraph C exponent T).ne_of_adj huw
    apply Subtype.ext
    exact h
  have hvwNe : v.1 ≠ w.1 := by
    intro h
    apply (enlargedCollisionGraph C exponent T).ne_of_adj hvw
    apply Subtype.ext
    exact h

  exact no_three_distinct_share_retained_completion
    C huvNe huwNe hvwNe
    hwordU hwordV hwordW



theorem projectedLoss_incident_collision_with_nonloss_is_retained
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexp : ∀ x, exponent x ≤ n)
    (honeLoss :
      ∀ x, (active C x).card ≤ n - exponent x + 1)
    {r u : V}
    (hrLoss : r ∈ projectedLossVertices C exponent)
    (hru : r ≠ u)
    (hcross :
      EnlargedBlocksCross C exponent r u) :
    if h : r < u then
      (C.color r u).val < n
    else
      (C.color u r).val < n := by
  have hrInactive :=
    residual_inactive_of_projectedLoss
      C exponent hexp honeLoss hrLoss
  by_cases hlt : r < u
  · simp [hlt]
    by_contra hnot
    have hres : IsResidual C r u := by
      unfold IsResidual residualCoord
      apply Fin.ext
      simp
      omega
    exact hrInactive
      (residualCoord_mem_active_of_isResidual
        C hlt hres).1
  · have hul : u < r := lt_of_le_of_ne
      (not_lt.mp hlt) hru.symm
    simp [hlt]
    by_contra hnot
    have hres : IsResidual C u r := by
      unfold IsResidual residualCoord
      apply Fin.ext
      simp
      omega
    exact hrInactive
      (residualCoord_mem_active_of_isResidual
        C hul hres).2

theorem oneLoss_twoNonloss_triangle_colour_shape
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexp : ∀ x, exponent x ≤ n)
    (honeLoss :
      ∀ x, (active C x).card ≤ n - exponent x + 1)
    (T : Finset V)
    {r u v : {x : V // x ∈ T}}
    (hru :
      (enlargedCollisionGraph C exponent T).Adj r u)
    (hrv :
      (enlargedCollisionGraph C exponent T).Adj r v)
    (huv :
      (enlargedCollisionGraph C exponent T).Adj u v)
    (hrLoss : r.1 ∈ projectedLossVertices C exponent)
    (huNonloss : u.1 ∉ projectedLossVertices C exponent)
    (hvNonloss : v.1 ∉ projectedLossVertices C exponent) :
    (
      if h : r.1 < u.1 then
        (C.color r.1 u.1).val < n
      else
        (C.color u.1 r.1).val < n
    )
    ∧
    (
      if h : r.1 < v.1 then
        (C.color r.1 v.1).val < n
      else
        (C.color v.1 r.1).val < n
    )
    ∧
    (
      (u.1 < v.1 ∧ IsResidual C u.1 v.1)
      ∨
      (v.1 < u.1 ∧ IsResidual C v.1 u.1)
    ) := by
  have hruCross :=
    enlargedCollisionGraph_cross_of_adj
      C exponent T hru
  have hrvCross :=
    enlargedCollisionGraph_cross_of_adj
      C exponent T hrv
  have huvCross :=
    enlargedCollisionGraph_cross_of_adj
      C exponent T huv
  have hruNe : r.1 ≠ u.1 := by
    intro h
    apply (enlargedCollisionGraph C exponent T).ne_of_adj hru
    apply Subtype.ext
    exact h
  have hrvNe : r.1 ≠ v.1 := by
    intro h
    apply (enlargedCollisionGraph C exponent T).ne_of_adj hrv
    apply Subtype.ext
    exact h
  obtain ⟨wordUV,huWord,hvWord⟩ := huvCross
  rw [enlargedProjectedCandidateBlock_nonloss
        C exponent huNonloss] at huWord
  rw [enlargedProjectedCandidateBlock_nonloss
        C exponent hvNonloss] at hvWord
  exact ⟨
    projectedLoss_incident_collision_with_nonloss_is_retained
      C exponent hexp honeLoss hrLoss hruNe hruCross,
    projectedLoss_incident_collision_with_nonloss_is_retained
      C exponent hexp honeLoss hrLoss hrvNe hrvCross,
    retainedCompletion_overlap_forces_residual
      C
      (by
        intro h
        apply (enlargedCollisionGraph C exponent T).ne_of_adj huv
        apply Subtype.ext
        exact h)
      huWord hvWord
  ⟩


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


theorem mem_coreEnlargedCandidateFibre_of_shared
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    {T : Finset V}
    {v : V}
    {word : Fin n → Bool}
    (hvT : v ∈ T)
    (hshared :
      word ∈ sharedBlockWords
        (enlargedProjectedCandidateBlock C exponent)
        T v) :
    v ∈ coreEnlargedCandidateFibre
      C exponent T word := by
  have hparts := Finset.mem_inter.mp hshared
  exact (mem_coreEnlargedCandidateFibre
    C exponent T word v).2 ⟨hvT,hparts.1⟩

theorem coreEnlargedCandidateFibre_card_eq_two_of_shared_of_three_lt_girth
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    {T : Finset V}
    (hgirth :
      3 < (enlargedCollisionGraph C exponent T).girth)
    {v : V}
    (hvT : v ∈ T)
    {word : Fin n → Bool}
    (hshared :
      word ∈ sharedBlockWords
        (enlargedProjectedCandidateBlock C exponent)
        T v) :
    (coreEnlargedCandidateFibre
      C exponent T word).card = 2 := by
  have hvF :=
    mem_coreEnlargedCandidateFibre_of_shared
      C exponent hvT hshared
  have hdata :=
    sharedBlockWords_has_other_block
      (enlargedProjectedCandidateBlock C exponent)
      hshared
  obtain ⟨_hvWord,w,hwT,hwv,hwWord⟩ := hdata
  have hwF :
      w ∈ coreEnlargedCandidateFibre
        C exponent T word :=
    (mem_coreEnlargedCandidateFibre
      C exponent T word w).2 ⟨hwT,hwWord⟩
  have htwo :
      2 ≤ (coreEnlargedCandidateFibre
        C exponent T word).card := by
    exact Finset.two_le_card.mpr ⟨v,hvF,w,hwF,hwv.symm⟩
  have hle :=
    coreEnlargedCandidateFibre_card_le_two_of_three_lt_girth
      C exponent T hgirth word
  omega

theorem shared_iff_mem_fibre_and_card_eq_two_of_three_lt_girth
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    {T : Finset V}
    (hgirth :
      3 < (enlargedCollisionGraph C exponent T).girth)
    {v : V}
    (hvT : v ∈ T)
    {word : Fin n → Bool} :
    word ∈ sharedBlockWords
        (enlargedProjectedCandidateBlock C exponent)
        T v
      ↔
    v ∈ coreEnlargedCandidateFibre C exponent T word
      ∧
    (coreEnlargedCandidateFibre
      C exponent T word).card = 2 := by
  constructor
  · intro hshared
    exact ⟨
      mem_coreEnlargedCandidateFibre_of_shared
        C exponent hvT hshared,
      coreEnlargedCandidateFibre_card_eq_two_of_shared_of_three_lt_girth
        C exponent hgirth hvT hshared
    ⟩
  · rintro ⟨hvF,hcard⟩
    have hvData :=
      (mem_coreEnlargedCandidateFibre
        C exponent T word v).1 hvF
    have hexists :
        ∃ w ∈ coreEnlargedCandidateFibre
            C exponent T word,
          w ≠ v := by
      by_contra hnot
      push_neg at hnot
      have hsub :
          coreEnlargedCandidateFibre
              C exponent T word
            ⊆ {v} := by
        intro w hw
        simpa [hnot w hw]
      have hle :=
        Finset.card_le_card hsub
      simp [hcard] at hle
    obtain ⟨w,hwF,hwv⟩ := hexists
    have hwData :=
      (mem_coreEnlargedCandidateFibre
        C exponent T word w).1 hwF
    apply Finset.mem_inter.mpr
    constructor
    · exact hvData.2
    · apply Finset.mem_biUnion.mpr
      exact ⟨w,
        Finset.mem_erase.mpr ⟨hwv,hwData.1⟩,
        hwData.2⟩


noncomputable def coreDoubleCoveredWords
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (T : Finset V) : Finset (Fin n → Bool) := by
  classical
  exact Finset.univ.filter fun word =>
    (coreEnlargedCandidateFibre C exponent T word).card = 2

@[simp] theorem mem_coreDoubleCoveredWords
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (T : Finset V)
    (word : Fin n → Bool) :
    word ∈ coreDoubleCoveredWords C exponent T ↔
      (coreEnlargedCandidateFibre C exponent T word).card = 2 := by
  classical
  simp [coreDoubleCoveredWords]

theorem mem_core_union_iff_fibre_nonempty
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (T : Finset V)
    (word : Fin n → Bool) :
    word ∈ T.biUnion (enlargedProjectedCandidateBlock C exponent)
      ↔
    (coreEnlargedCandidateFibre C exponent T word).Nonempty := by
  classical
  constructor
  · intro hword
    obtain ⟨v,hvT,hvWord⟩ := Finset.mem_biUnion.mp hword
    exact ⟨v,
      (mem_coreEnlargedCandidateFibre
        C exponent T word v).2 ⟨hvT,hvWord⟩⟩
  · rintro ⟨v,hvF⟩
    have hvData :=
      (mem_coreEnlargedCandidateFibre
        C exponent T word v).1 hvF
    exact Finset.mem_biUnion.mpr
      ⟨v,hvData.1,hvData.2⟩

theorem sum_coreEnlargedCandidateFibre_cards_eq_sum_block_cards
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (T : Finset V) :
    (∑ word : Fin n → Bool,
      (coreEnlargedCandidateFibre
        C exponent T word).card)
      =
    ∑ v ∈ T,
      (enlargedProjectedCandidateBlock
        C exponent v).card := by
  classical
  calc
    (∑ word : Fin n → Bool,
      (coreEnlargedCandidateFibre
        C exponent T word).card)
      =
    ∑ word : Fin n → Bool,
      ∑ v ∈ T,
        if word ∈ enlargedProjectedCandidateBlock C exponent v
        then 1 else 0 := by
      apply Finset.sum_congr rfl
      intro word hword
      rw [show
        coreEnlargedCandidateFibre C exponent T word =
          T.filter fun v =>
            word ∈ enlargedProjectedCandidateBlock C exponent v by
          simp [coreEnlargedCandidateFibre]]
      rw [Finset.card_filter]
    _ =
    ∑ v ∈ T,
      ∑ word : Fin n → Bool,
        if word ∈ enlargedProjectedCandidateBlock C exponent v
        then 1 else 0 := by
      rw [Finset.sum_comm]
    _ =
    ∑ v ∈ T,
      (enlargedProjectedCandidateBlock
        C exponent v).card := by
      apply Finset.sum_congr rfl
      intro v hvT
      symm
      exact Finset.card_eq_sum_ite
        (Finset.subset_univ
          (enlargedProjectedCandidateBlock C exponent v))

theorem sum_fibre_cards_eq_union_add_double_of_card_le_two
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (T : Finset V)
    (hle :
      ∀ word : Fin n → Bool,
        (coreEnlargedCandidateFibre
          C exponent T word).card ≤ 2) :
    (∑ word : Fin n → Bool,
      (coreEnlargedCandidateFibre
        C exponent T word).card)
      =
    (T.biUnion
      (enlargedProjectedCandidateBlock C exponent)).card
      +
    (coreDoubleCoveredWords C exponent T).card := by
  classical
  have hpoint :
      ∀ word : Fin n → Bool,
        (coreEnlargedCandidateFibre
          C exponent T word).card
        =
        (if word ∈ T.biUnion
              (enlargedProjectedCandidateBlock C exponent)
         then 1 else 0)
        +
        (if word ∈ coreDoubleCoveredWords C exponent T
         then 1 else 0) := by
    intro word
    have hcard := hle word
    have hunion :=
      mem_core_union_iff_fibre_nonempty
        C exponent T word
    have hdouble :=
      mem_coreDoubleCoveredWords
        C exponent T word
    by_cases hzero :
        (coreEnlargedCandidateFibre
          C exponent T word).card = 0
    · have hnotUnion :
          word ∉ T.biUnion
            (enlargedProjectedCandidateBlock C exponent) := by
        intro hmem
        have hne :=
          (Finset.card_pos.mpr
            (hunion.mp hmem))
        omega
      have hnotDouble :
          word ∉ coreDoubleCoveredWords C exponent T := by
        intro hd
        have hd2 := hdouble.mp hd
        omega
      simp [hzero,hnotUnion,hnotDouble]
    · have hpos :
          0 < (coreEnlargedCandidateFibre
            C exponent T word).card := by omega
      have hUnion :
          word ∈ T.biUnion
            (enlargedProjectedCandidateBlock C exponent) :=
        hunion.mpr (Finset.card_pos.mp hpos)
      by_cases htwo :
          (coreEnlargedCandidateFibre
            C exponent T word).card = 2
      · have hDouble :
            word ∈ coreDoubleCoveredWords C exponent T :=
          hdouble.mpr htwo
        simp [hUnion,hDouble,htwo]
      · have hone :
            (coreEnlargedCandidateFibre
              C exponent T word).card = 1 := by
          omega
        have hnotDouble :
            word ∉ coreDoubleCoveredWords C exponent T := by
          intro hd
          exact htwo (hdouble.mp hd)
        simp [hUnion,hnotDouble,hone]

  calc
    (∑ word : Fin n → Bool,
      (coreEnlargedCandidateFibre
        C exponent T word).card)
      =
    ∑ word : Fin n → Bool,
      (
        (if word ∈ T.biUnion
              (enlargedProjectedCandidateBlock C exponent)
         then 1 else 0)
        +
        (if word ∈ coreDoubleCoveredWords C exponent T
         then 1 else 0)
      ) := by
        apply Finset.sum_congr rfl
        intro word hword
        exact hpoint word
    _ =
      (∑ word : Fin n → Bool,
        if word ∈ T.biUnion
              (enlargedProjectedCandidateBlock C exponent)
        then 1 else 0)
      +
      (∑ word : Fin n → Bool,
        if word ∈ coreDoubleCoveredWords C exponent T
        then 1 else 0) := by
        rw [Finset.sum_add_distrib]
    _ =
    (T.biUnion
      (enlargedProjectedCandidateBlock C exponent)).card
      +
    (coreDoubleCoveredWords C exponent T).card := by
      congr 1
      · symm
        exact Finset.card_eq_sum_ite
          (Finset.subset_univ
            (T.biUnion
              (enlargedProjectedCandidateBlock C exponent)))
      · symm
        exact Finset.card_eq_sum_ite
          (Finset.subset_univ
            (coreDoubleCoveredWords C exponent T))

theorem longCycle_sum_block_cards_eq_union_add_double
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (T : Finset V)
    (hgirth :
      3 < (enlargedCollisionGraph C exponent T).girth) :
    (∑ v ∈ T,
      (enlargedProjectedCandidateBlock
        C exponent v).card)
      =
    (T.biUnion
      (enlargedProjectedCandidateBlock C exponent)).card
      +
    (coreDoubleCoveredWords C exponent T).card := by
  rw [← sum_coreEnlargedCandidateFibre_cards_eq_sum_block_cards
    C exponent T]
  exact sum_fibre_cards_eq_union_add_double_of_card_le_two
    C exponent T
    (coreEnlargedCandidateFibre_card_le_two_of_three_lt_girth
      C exponent T hgirth)



theorem longCycle_sum_shared_cards_eq_two_mul_doubleCovered
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    {T : Finset V}
    (hgirth :
      3 < (enlargedCollisionGraph C exponent T).girth) :
    (∑ v ∈ T,
      (sharedBlockWords
        (enlargedProjectedCandidateBlock C exponent)
        T v).card)
      =
    2 * (coreDoubleCoveredWords C exponent T).card := by
  classical
  have hpoint :
      ∀ word : Fin n → Bool,
        (∑ v ∈ T,
          if word ∈ sharedBlockWords
              (enlargedProjectedCandidateBlock C exponent)
              T v
          then 1 else 0)
        =
        if word ∈ coreDoubleCoveredWords C exponent T
        then 2 else 0 := by
    intro word
    by_cases hdouble :
        word ∈ coreDoubleCoveredWords C exponent T
    · have hcard :=
        (mem_coreDoubleCoveredWords
          C exponent T word).1 hdouble
      have hfilterEq :
          T.filter
              (fun v =>
                word ∈ sharedBlockWords
                  (enlargedProjectedCandidateBlock C exponent)
                  T v)
            =
          coreEnlargedCandidateFibre
            C exponent T word := by
        ext v
        simp only [Finset.mem_filter]
        constructor
        · rintro ⟨hvT,hshared⟩
          exact mem_coreEnlargedCandidateFibre_of_shared
            C exponent hvT hshared
        · intro hvF
          have hvData :=
            (mem_coreEnlargedCandidateFibre
              C exponent T word v).1 hvF
          refine ⟨hvData.1,?_⟩
          exact
            (shared_iff_mem_fibre_and_card_eq_two_of_three_lt_girth
              C exponent hgirth hvData.1).2
              ⟨hvF,hcard⟩
      calc
        (∑ v ∈ T,
          if word ∈ sharedBlockWords
              (enlargedProjectedCandidateBlock C exponent)
              T v
          then 1 else 0)
          =
        (T.filter
          (fun v =>
            word ∈ sharedBlockWords
              (enlargedProjectedCandidateBlock C exponent)
              T v)).card := by
            symm
            exact Finset.card_filter _ _
        _ =
        (coreEnlargedCandidateFibre
          C exponent T word).card := by rw [hfilterEq]
        _ = 2 := hcard
        _ =
        if word ∈ coreDoubleCoveredWords C exponent T
        then 2 else 0 := by simp [hdouble]
    · have hnone :
          ∀ v ∈ T,
            word ∉ sharedBlockWords
              (enlargedProjectedCandidateBlock C exponent)
              T v := by
        intro v hvT hshared
        have hcard :=
          coreEnlargedCandidateFibre_card_eq_two_of_shared_of_three_lt_girth
            C exponent hgirth hvT hshared
        exact hdouble
          ((mem_coreDoubleCoveredWords
            C exponent T word).2 hcard)
      simp [hdouble,hnone]

  calc
    (∑ v ∈ T,
      (sharedBlockWords
        (enlargedProjectedCandidateBlock C exponent)
        T v).card)
      =
    ∑ v ∈ T,
      ∑ word : Fin n → Bool,
        if word ∈ sharedBlockWords
            (enlargedProjectedCandidateBlock C exponent)
            T v
        then 1 else 0 := by
          apply Finset.sum_congr rfl
          intro v hvT
          symm
          exact Finset.card_eq_sum_ite
            (Finset.subset_univ
              (sharedBlockWords
                (enlargedProjectedCandidateBlock C exponent)
                T v))
    _ =
    ∑ word : Fin n → Bool,
      ∑ v ∈ T,
        if word ∈ sharedBlockWords
            (enlargedProjectedCandidateBlock C exponent)
            T v
        then 1 else 0 := by
          rw [Finset.sum_comm]
    _ =
    ∑ word : Fin n → Bool,
      if word ∈ coreDoubleCoveredWords C exponent T
      then 2 else 0 := by
          apply Finset.sum_congr rfl
          intro word hword
          exact hpoint word
    _ =
    2 * (coreDoubleCoveredWords C exponent T).card := by
      have hcard :
          (coreDoubleCoveredWords C exponent T).card
            =
          ∑ word : Fin n → Bool,
            if word ∈ coreDoubleCoveredWords C exponent T
            then 1 else 0 := by
        exact Finset.card_eq_sum_ite
          (Finset.subset_univ
            (coreDoubleCoveredWords C exponent T))
      rw [hcard, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro word hword
      by_cases hmem :
          word ∈ coreDoubleCoveredWords C exponent T
      · simp [hmem]
      · simp [hmem]


theorem longCycle_doubleCovered_eq_totalSlack_add_deficiency
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
    (hgirth :
      3 < (enlargedCollisionGraph C exponent T).girth) :
    (coreDoubleCoveredWords C exponent T).card
      =
    (∑ v ∈ T,
      (
        (enlargedProjectedCandidateBlock C exponent v).card -
          2 ^ exponent v
      ))
      +
    blockDeficiencyAmount
      (fun x => 2 ^ exponent x)
      (enlargedProjectedCandidateBlock C exponent)
      T := by
  classical
  have hcount :=
    longCycle_sum_block_cards_eq_union_add_double
      C exponent T hgirth

  have hlocal :
      ∀ v : V,
        2 ^ exponent v ≤
          (enlargedProjectedCandidateBlock
            C exponent v).card :=
    enlargedProjectedCandidateBlock_local_capacity
      C exponent hexpLt hexp honeLoss

  have hslackAdd :
      (∑ v ∈ T,
        (
          (enlargedProjectedCandidateBlock C exponent v).card -
            2 ^ exponent v
        ))
        +
      (∑ v ∈ T, 2 ^ exponent v)
      =
      ∑ v ∈ T,
        (enlargedProjectedCandidateBlock C exponent v).card := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro v hvT
    exact Nat.sub_add_cancel (hlocal v)

  have hdef' :
      (T.biUnion
        (enlargedProjectedCandidateBlock C exponent)).card
        <
      ∑ v ∈ T, 2 ^ exponent v := hdef

  unfold blockDeficiencyAmount
  omega


theorem longCycle_sum_shared_eq_two_slack_add_two_deficiency
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
    (hgirth :
      3 < (enlargedCollisionGraph C exponent T).girth) :
    (∑ v ∈ T,
      (sharedBlockWords
        (enlargedProjectedCandidateBlock C exponent)
        T v).card)
      =
    2 *
      (∑ v ∈ T,
        (
          (enlargedProjectedCandidateBlock C exponent v).card -
            2 ^ exponent v
        ))
      +
    2 *
      blockDeficiencyAmount
        (fun x => 2 ^ exponent x)
        (enlargedProjectedCandidateBlock C exponent)
        T := by
  have hshared :=
    longCycle_sum_shared_cards_eq_two_mul_doubleCovered
      C exponent hgirth
  have hdouble :=
    longCycle_doubleCovered_eq_totalSlack_add_deficiency
      C exponent hexpLt hexp honeLoss
      hdef hgirth
  rw [hdouble] at hshared
  omega

theorem longCycle_exists_shared_overload_vertex
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
    (hgirth :
      3 < (enlargedCollisionGraph C exponent T).girth) :
    ∃ v ∈ T,
      2 *
        (
          (enlargedProjectedCandidateBlock C exponent v).card -
            2 ^ exponent v
        )
        <
      (sharedBlockWords
        (enlargedProjectedCandidateBlock C exponent)
        T v).card := by
  classical
  by_contra hnone
  push_neg at hnone
  have hsumLe :
      (∑ v ∈ T,
        (sharedBlockWords
          (enlargedProjectedCandidateBlock C exponent)
          T v).card)
        ≤
      2 *
        (∑ v ∈ T,
          (
            (enlargedProjectedCandidateBlock C exponent v).card -
              2 ^ exponent v
          )) := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun v hv =>
      hnone v hv
  have heq :=
    longCycle_sum_shared_eq_two_slack_add_two_deficiency
      C exponent hexpLt hexp honeLoss
      hdef hgirth
  have hpos :=
    blockDeficiencyAmount_pos_of_deficient
      (fun x : V => 2 ^ exponent x)
      (enlargedProjectedCandidateBlock C exponent)
      hdef
  omega

theorem longCycle_shared_overload_exact_or_topLoss
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexpLt : ∀ x, exponent x < n)
    (hexp : ∀ x, exponent x ≤ n)
    (honeLoss :
      ∀ x, (active C x).card ≤ n - exponent x + 1)
    {T : Finset V}
    {v : V}
    (hvT : v ∈ T)
    (hover :
      2 *
        (
          (enlargedProjectedCandidateBlock C exponent v).card -
            2 ^ exponent v
        )
        <
      (sharedBlockWords
        (enlargedProjectedCandidateBlock C exponent)
        T v).card) :
    ExactProjectedBudget C exponent v
    ∨
    (
      v ∈ projectedLossVertices C exponent
      ∧ exponent v = n - 1
    ) := by
  classical
  rcases projectedProfile_strict_exact_or_loss
      C exponent hexp honeLoss v
    with hstrict | hexact | hloss
  · have hblock :=
      strict_enlargedBlock_card_le_two_mul_localSlack
        C exponent hstrict
    have hsharedLe :
        (sharedBlockWords
          (enlargedProjectedCandidateBlock C exponent)
          T v).card
          ≤
        (enlargedProjectedCandidateBlock C exponent v).card := by
      exact Finset.card_le_card
        (sharedBlockWords_subset_block
          (enlargedProjectedCandidateBlock C exponent) T v)
    omega
  · exact Or.inl hexact
  · by_cases htop : exponent v = n - 1
    · exact Or.inr ⟨hloss,htop⟩
    · have hlower :
          exponent v + 2 ≤ n := by
        have hlt := hexpLt v
        omega
      have hblock :=
        lowerLoss_enlargedBlock_card_le_two_mul_localSlack
          C exponent hloss hlower
      have hsharedLe :
          (sharedBlockWords
            (enlargedProjectedCandidateBlock C exponent)
            T v).card
            ≤
          (enlargedProjectedCandidateBlock C exponent v).card := by
        exact Finset.card_le_card
          (sharedBlockWords_subset_block
            (enlargedProjectedCandidateBlock C exponent) T v)
      omega

theorem longCycle_exists_exact_or_topLoss_overload
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
    (hgirth :
      3 < (enlargedCollisionGraph C exponent T).girth) :
    ∃ v ∈ T,
      (
        ExactProjectedBudget C exponent v
        ∨
        (
          v ∈ projectedLossVertices C exponent
          ∧ exponent v = n - 1
        )
      )
      ∧
      2 *
        (
          (enlargedProjectedCandidateBlock C exponent v).card -
            2 ^ exponent v
        )
        <
      (sharedBlockWords
        (enlargedProjectedCandidateBlock C exponent)
        T v).card := by
  obtain ⟨v,hvT,hover⟩ :=
    longCycle_exists_shared_overload_vertex
      C exponent hexpLt hexp honeLoss
      hdef hgirth
  exact ⟨v,hvT,
    longCycle_shared_overload_exact_or_topLoss
      C exponent hexpLt hexp honeLoss
      hvT hover,
    hover⟩



theorem topLoss_localSlack_eq_completionCube
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    {v : V}
    (hvLoss : v ∈ projectedLossVertices C exponent)
    (hvTop : exponent v = n - 1) :
    (enlargedProjectedCandidateBlock C exponent v).card -
        2 ^ exponent v
      =
    (retainedCompletionWords C v).card := by
  have hactive :=
    topLoss_retainedActive_card_eq_two
      C exponent hvLoss hvTop
  rw [enlargedProjectedCandidateBlock_loss
        C exponent hvLoss,
      allActiveLossCandidateBlock_card,
      projectedLoss_target_eq_two_mul_completion
        C exponent hvLoss,
      hactive]
  omega

theorem topLoss_overload_has_shared_completion_word
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    {T : Finset V}
    {v : V}
    (hvLoss : v ∈ projectedLossVertices C exponent)
    (hvTop : exponent v = n - 1)
    (hover :
      2 *
        (
          (enlargedProjectedCandidateBlock C exponent v).card -
            2 ^ exponent v
        )
        <
      (sharedBlockWords
        (enlargedProjectedCandidateBlock C exponent)
        T v).card) :
    (
      sharedBlockWords
        (enlargedProjectedCandidateBlock C exponent)
        T v
      ∩
      retainedCompletionWords C v
    ).Nonempty := by
  classical
  have hslack :=
    topLoss_localSlack_eq_completionCube
      C exponent hvLoss hvTop
  rw [hslack] at hover
  by_contra hempty
  have hinterEmpty :
      sharedBlockWords
          (enlargedProjectedCandidateBlock C exponent)
          T v
        ∩
      retainedCompletionWords C v = ∅ :=
    Finset.not_nonempty_iff_eq_empty.mp hempty
  have hsub :
      sharedBlockWords
          (enlargedProjectedCandidateBlock C exponent)
          T v
        ⊆
      allActiveTranslatedWords C v := by
    intro word hshared
    have hblock :=
      (sharedBlockWords_subset_block
        (enlargedProjectedCandidateBlock C exponent)
        T v) hshared
    rw [enlargedProjectedCandidateBlock_loss
      C exponent hvLoss] at hblock
    unfold allActiveLossCandidateBlock at hblock
    rcases Finset.mem_union.mp hblock with hQ | hT
    · have hboth :
          word ∈
            sharedBlockWords
              (enlargedProjectedCandidateBlock C exponent)
              T v
            ∩
            retainedCompletionWords C v :=
        Finset.mem_inter.mpr ⟨hshared,hQ⟩
      rw [hinterEmpty] at hboth
      exact False.elim (by simpa using hboth)
    · exact hT
  have hcardLe :=
    Finset.card_le_card hsub
  have hactive :=
    topLoss_retainedActive_card_eq_two
      C exponent hvLoss hvTop
  rw [allActiveTranslatedWords_card,hactive] at hcardLe
  omega

#print axioms topLoss_localSlack_eq_completionCube
#print axioms topLoss_overload_has_shared_completion_word


inductive ExactSharedOutlet
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (v : V) : Prop
  | strictPaid
      (w : V)
      (hwStrict : exponent w < projectedFree C w)
      (hpaid :
        (retainedCompletionWords C v ∩
          retainedCompletionWords C w).card
          ≤
        dyadicProfileSurplus exponent (projectedFree C) w)
  | strictUnpaid
      (w : V)
      (hrel : MixedUnpaidChild C exponent v w)
  | exactPair
      (w : V)
      (hvw : v ≠ w)
      (hwExact : ExactProjectedBudget C exponent w)
      (word : Fin n → Bool)
      (hvWord : word ∈ retainedCompletionWords C v)
      (hwWord : word ∈ retainedCompletionWords C w)
  | loss
      (w : V)
      (hvw : v ≠ w)
      (hwLoss : w ∈ projectedLossVertices C exponent)

theorem exactSharedOutlet_of_shared_word
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexp : ∀ x, exponent x ≤ n)
    (honeLoss :
      ∀ x, (active C x).card ≤ n - exponent x + 1)
    {T : Finset V}
    {v : V}
    (hvT : v ∈ T)
    (hvExact : ExactProjectedBudget C exponent v)
    {word : Fin n → Bool}
    (hshared :
      word ∈ sharedBlockWords
        (enlargedProjectedCandidateBlock C exponent)
        T v) :
    ExactSharedOutlet C exponent v := by
  classical
  have hvNonloss :
      v ∉ projectedLossVertices C exponent := by
    intro hvLoss
    have heq :=
      (mem_projectedLossVertices C exponent v).1 hvLoss
    unfold ExactProjectedBudget at hvExact
    omega
  have hdata :=
    sharedBlockWords_has_other_block
      (enlargedProjectedCandidateBlock C exponent)
      hshared
  obtain ⟨hvBlock,w,hwT,hwv,hwBlock⟩ := hdata
  have hvWord :
      word ∈ retainedCompletionWords C v := by
    rw [enlargedProjectedCandidateBlock_nonloss
      C exponent hvNonloss] at hvBlock
    exact hvBlock

  rcases projectedProfile_strict_exact_or_loss
      C exponent hexp honeLoss w
    with hwStrict | hwExact | hwLoss
  · have hwNonloss :
        w ∉ projectedLossVertices C exponent := by
      intro hwLoss'
      have heq :=
        (mem_projectedLossVertices C exponent w).1 hwLoss'
      omega
    have hwWord :
        word ∈ retainedCompletionWords C w := by
      rw [enlargedProjectedCandidateBlock_nonloss
        C exponent hwNonloss] at hwBlock
      exact hwBlock
    by_cases hpaid :
        (retainedCompletionWords C v ∩
          retainedCompletionWords C w).card
          ≤
        dyadicProfileSurplus exponent (projectedFree C) w
    · exact ExactSharedOutlet.strictPaid
        w hwStrict hpaid
    · exact ExactSharedOutlet.strictUnpaid
        w
        ⟨hwv.symm,hvExact,hwStrict,
          word,hvWord,hwWord,hpaid⟩
  · have hwNonloss :
        w ∉ projectedLossVertices C exponent := by
      intro hwLoss'
      have heq :=
        (mem_projectedLossVertices C exponent w).1 hwLoss'
      unfold ExactProjectedBudget at hwExact
      omega
    have hwWord :
        word ∈ retainedCompletionWords C w := by
      rw [enlargedProjectedCandidateBlock_nonloss
        C exponent hwNonloss] at hwBlock
      exact hwBlock
    exact ExactSharedOutlet.exactPair
      w hwv.symm hwExact word hvWord hwWord
  · exact ExactSharedOutlet.loss
      w hwv.symm hwLoss

theorem longCycle_exact_overload_has_shared_outlet
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexp : ∀ x, exponent x ≤ n)
    (honeLoss :
      ∀ x, (active C x).card ≤ n - exponent x + 1)
    {T : Finset V}
    {v : V}
    (hvT : v ∈ T)
    (hvExact : ExactProjectedBudget C exponent v)
    (hover :
      2 *
        (
          (enlargedProjectedCandidateBlock C exponent v).card -
            2 ^ exponent v
        )
        <
      (sharedBlockWords
        (enlargedProjectedCandidateBlock C exponent)
        T v).card) :
    ExactSharedOutlet C exponent v := by
  have hsharedPos :
      0 <
      (sharedBlockWords
        (enlargedProjectedCandidateBlock C exponent)
        T v).card := by
    omega
  obtain ⟨word,hword⟩ :=
    Finset.card_pos.mp hsharedPos
  exact exactSharedOutlet_of_shared_word
    C exponent hexp honeLoss
    hvT hvExact hword

#print axioms exactSharedOutlet_of_shared_word
#print axioms longCycle_exact_overload_has_shared_outlet


theorem longCycle_overload_recursive_outlet
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
    (hgirth :
      3 < (enlargedCollisionGraph C exponent T).girth) :
    (
      ∃ v ∈ T,
        ExactProjectedBudget C exponent v ∧
        ExactSharedOutlet C exponent v
    )
    ∨
    (
      ∃ v ∈ T,
        v ∈ projectedLossVertices C exponent ∧
        exponent v = n - 1 ∧
        (
          sharedBlockWords
            (enlargedProjectedCandidateBlock C exponent)
            T v
          ∩
          retainedCompletionWords C v
        ).Nonempty
    ) := by
  obtain ⟨v,hvT,hprofile,hover⟩ :=
    longCycle_exists_exact_or_topLoss_overload
      C exponent hexpLt hexp honeLoss
      hdef hgirth
  rcases hprofile with hvExact | ⟨hvLoss,hvTop⟩
  · exact Or.inl
      ⟨v,hvT,hvExact,
        longCycle_exact_overload_has_shared_outlet
          C exponent hexp honeLoss
          hvT hvExact hover⟩
  · exact Or.inr
      ⟨v,hvT,hvLoss,hvTop,
        topLoss_overload_has_shared_completion_word
          C exponent hvLoss hvTop hover⟩

#print axioms longCycle_overload_recursive_outlet

theorem longCycle_totalSlack_lt_doubleCovered
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
    (hgirth :
      3 < (enlargedCollisionGraph C exponent T).girth) :
    (∑ v ∈ T,
      (
        (enlargedProjectedCandidateBlock C exponent v).card -
          2 ^ exponent v
      ))
      <
    (coreDoubleCoveredWords C exponent T).card := by
  have heq :=
    longCycle_doubleCovered_eq_totalSlack_add_deficiency
      C exponent hexpLt hexp honeLoss
      hdef hgirth
  have hpos :=
    blockDeficiencyAmount_pos_of_deficient
      (fun x : V => 2 ^ exponent x)
      (enlargedProjectedCandidateBlock C exponent)
      hdef
  omega


noncomputable def coreOrderedVertexPairs
    {V : Type*} [LinearOrder V]
    (T : Finset V) : Finset (V × V) := by
  classical
  exact (T.product T).filter fun uv => uv.1 < uv.2

noncomputable def corePairOverlapWords
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (uv : V × V) : Finset (Fin n → Bool) :=
  enlargedProjectedCandidateBlock C exponent uv.1 ∩
    enlargedProjectedCandidateBlock C exponent uv.2

@[simp] theorem mem_coreOrderedVertexPairs
    {V : Type*} [LinearOrder V]
    (T : Finset V)
    (u v : V) :
    (u,v) ∈ coreOrderedVertexPairs T ↔
      u ∈ T ∧ v ∈ T ∧ u < v := by
  classical
  simp [coreOrderedVertexPairs, and_assoc]

theorem longCycle_doubleCoveredWords_eq_pairOverlapUnion
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (T : Finset V)
    (hgirth :
      3 < (enlargedCollisionGraph C exponent T).girth) :
    coreDoubleCoveredWords C exponent T
      =
    (coreOrderedVertexPairs T).biUnion
      (corePairOverlapWords C exponent) := by
  classical
  ext word
  constructor
  · intro hdouble
    have hcard :=
      (mem_coreDoubleCoveredWords
        C exponent T word).1 hdouble
    obtain ⟨u,v,huv,hfib⟩ :=
      Finset.card_eq_two.mp hcard
    have huF :
        u ∈ coreEnlargedCandidateFibre
          C exponent T word := by
      rw [hfib]
      simp
    have hvF :
        v ∈ coreEnlargedCandidateFibre
          C exponent T word := by
      rw [hfib]
      simp
    have huData :=
      (mem_coreEnlargedCandidateFibre
        C exponent T word u).1 huF
    have hvData :=
      (mem_coreEnlargedCandidateFibre
        C exponent T word v).1 hvF
    rcases lt_or_gt_of_ne huv with huvlt | hvult
    · apply Finset.mem_biUnion.mpr
      refine ⟨(u,v),?_,?_⟩
      · exact (mem_coreOrderedVertexPairs T u v).2
          ⟨huData.1,hvData.1,huvlt⟩
      · exact Finset.mem_inter.mpr
          ⟨huData.2,hvData.2⟩
    · apply Finset.mem_biUnion.mpr
      refine ⟨(v,u),?_,?_⟩
      · exact (mem_coreOrderedVertexPairs T v u).2
          ⟨hvData.1,huData.1,hvult⟩
      · exact Finset.mem_inter.mpr
          ⟨hvData.2,huData.2⟩
  · intro hunion
    obtain ⟨uv,huvPair,hwordPair⟩ :=
      Finset.mem_biUnion.mp hunion
    rcases uv with ⟨u,v⟩
    have hpair :=
      (mem_coreOrderedVertexPairs T u v).1 huvPair
    have hwordParts :=
      Finset.mem_inter.mp hwordPair
    have huF :
        u ∈ coreEnlargedCandidateFibre
          C exponent T word :=
      (mem_coreEnlargedCandidateFibre
        C exponent T word u).2
        ⟨hpair.1,hwordParts.1⟩
    have hvF :
        v ∈ coreEnlargedCandidateFibre
          C exponent T word :=
      (mem_coreEnlargedCandidateFibre
        C exponent T word v).2
        ⟨hpair.2.1,hwordParts.2⟩
    have htwo :
        2 ≤ (coreEnlargedCandidateFibre
          C exponent T word).card := by
      exact Finset.two_le_card.mpr
        ⟨u,huF,v,hvF,ne_of_lt hpair.2.2⟩
    have hle :=
      coreEnlargedCandidateFibre_card_le_two_of_three_lt_girth
        C exponent T hgirth word
    apply (mem_coreDoubleCoveredWords
      C exponent T word).2
    omega

theorem longCycle_doubleCovered_card_le_sum_pairOverlaps
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (T : Finset V)
    (hgirth :
      3 < (enlargedCollisionGraph C exponent T).girth) :
    (coreDoubleCoveredWords C exponent T).card
      ≤
    ∑ uv ∈ coreOrderedVertexPairs T,
      (corePairOverlapWords C exponent uv).card := by
  rw [longCycle_doubleCoveredWords_eq_pairOverlapUnion
    C exponent T hgirth]
  exact Finset.card_biUnion_le

theorem longCycle_totalSlack_lt_sum_pairOverlaps
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
    (hgirth :
      3 < (enlargedCollisionGraph C exponent T).girth) :
    (∑ v ∈ T,
      (
        (enlargedProjectedCandidateBlock C exponent v).card -
          2 ^ exponent v
      ))
      <
    ∑ uv ∈ coreOrderedVertexPairs T,
      (corePairOverlapWords C exponent uv).card := by
  exact lt_of_lt_of_le
    (longCycle_totalSlack_lt_doubleCovered
      C exponent hexpLt hexp honeLoss hdef hgirth)
    (longCycle_doubleCovered_card_le_sum_pairOverlaps
      C exponent T hgirth)


theorem ordered_pair_eq_of_pair_finset_eq
    {V : Type*} [LinearOrder V]
    {u v x y : V}
    (huv : u < v)
    (hxy : x < y)
    (hset : ({u,v} : Finset V) = {x,y}) :
    (u,v) = (x,y) := by
  classical
  have huMem : u ∈ ({x,y} : Finset V) := by
    rw [← hset]
    simp
  have hvMem : v ∈ ({x,y} : Finset V) := by
    rw [← hset]
    simp
  have hu : u = x ∨ u = y := by
    simpa [Finset.mem_insert, Finset.mem_singleton] using huMem
  have hv : v = x ∨ v = y := by
    simpa [Finset.mem_insert, Finset.mem_singleton] using hvMem
  rcases hu with hux | huy
  · subst x
    rcases hv with hvu | hvy
    · subst v
      exact False.elim ((lt_irrefl u) huv)
    · subst y
      rfl
  · subst y
    rcases hv with hvx | hvu
    · subst x
      exact False.elim (lt_asymm huv hxy)
    · subst v
      exact False.elim ((lt_irrefl u) huv)

theorem longCycle_pairOverlapWords_pairwiseDisjoint
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (T : Finset V)
    (hgirth :
      3 < (enlargedCollisionGraph C exponent T).girth) :
    ((coreOrderedVertexPairs T : Finset (V × V)) : Set (V × V)).PairwiseDisjoint
      (corePairOverlapWords C exponent) := by
  classical
  intro p hp q hq hpq
  rcases p with ⟨u,v⟩
  rcases q with ⟨x,y⟩
  have hpData :=
    (mem_coreOrderedVertexPairs T u v).1 hp
  have hqData :=
    (mem_coreOrderedVertexPairs T x y).1 hq
  rw [Finset.disjoint_left]
  intro word hpWord hqWord
  have hpParts := Finset.mem_inter.mp hpWord
  have hqParts := Finset.mem_inter.mp hqWord

  have huF :
      u ∈ coreEnlargedCandidateFibre
        C exponent T word :=
    (mem_coreEnlargedCandidateFibre
      C exponent T word u).2
      ⟨hpData.1,hpParts.1⟩
  have hvF :
      v ∈ coreEnlargedCandidateFibre
        C exponent T word :=
    (mem_coreEnlargedCandidateFibre
      C exponent T word v).2
      ⟨hpData.2.1,hpParts.2⟩
  have hxF :
      x ∈ coreEnlargedCandidateFibre
        C exponent T word :=
    (mem_coreEnlargedCandidateFibre
      C exponent T word x).2
      ⟨hqData.1,hqParts.1⟩
  have hyF :
      y ∈ coreEnlargedCandidateFibre
        C exponent T word :=
    (mem_coreEnlargedCandidateFibre
      C exponent T word y).2
      ⟨hqData.2.1,hqParts.2⟩

  have hle :=
    coreEnlargedCandidateFibre_card_le_two_of_three_lt_girth
      C exponent T hgirth word
  have htwo :
      2 ≤ (coreEnlargedCandidateFibre
        C exponent T word).card := by
    exact Finset.two_le_card.mpr
      ⟨u,huF,v,hvF,ne_of_lt hpData.2.2⟩
  have hcard :
      (coreEnlargedCandidateFibre
        C exponent T word).card = 2 := by
    omega

  have hpSubset :
      ({u,v} : Finset V) ⊆
        coreEnlargedCandidateFibre
          C exponent T word := by
    intro z hz
    simp only [Finset.mem_insert, Finset.mem_singleton] at hz
    rcases hz with rfl | rfl
    · exact huF
    · exact hvF
  have hqSubset :
      ({x,y} : Finset V) ⊆
        coreEnlargedCandidateFibre
          C exponent T word := by
    intro z hz
    simp only [Finset.mem_insert, Finset.mem_singleton] at hz
    rcases hz with rfl | rfl
    · exact hxF
    · exact hyF

  have hpEq :
      ({u,v} : Finset V) =
        coreEnlargedCandidateFibre
          C exponent T word := by
    apply Finset.eq_of_subset_of_card_le hpSubset
    simpa [hcard, ne_of_lt hpData.2.2]
  have hqEq :
      ({x,y} : Finset V) =
        coreEnlargedCandidateFibre
          C exponent T word := by
    apply Finset.eq_of_subset_of_card_le hqSubset
    simpa [hcard, ne_of_lt hqData.2.2]

  have hpqEq : (u,v) = (x,y) :=
    ordered_pair_eq_of_pair_finset_eq
      hpData.2.2 hqData.2.2
      (hpEq.trans hqEq.symm)
  exact hpq hpqEq

theorem longCycle_doubleCovered_card_eq_sum_pairOverlaps
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (T : Finset V)
    (hgirth :
      3 < (enlargedCollisionGraph C exponent T).girth) :
    (coreDoubleCoveredWords C exponent T).card
      =
    ∑ uv ∈ coreOrderedVertexPairs T,
      (corePairOverlapWords C exponent uv).card := by
  rw [longCycle_doubleCoveredWords_eq_pairOverlapUnion
    C exponent T hgirth]
  exact Finset.card_biUnion
    (longCycle_pairOverlapWords_pairwiseDisjoint
      C exponent T hgirth)

theorem longCycle_sum_pairOverlaps_eq_totalSlack_add_deficiency
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
    (hgirth :
      3 < (enlargedCollisionGraph C exponent T).girth) :
    (∑ uv ∈ coreOrderedVertexPairs T,
      (corePairOverlapWords C exponent uv).card)
      =
    (∑ v ∈ T,
      (
        (enlargedProjectedCandidateBlock C exponent v).card -
          2 ^ exponent v
      ))
      +
    blockDeficiencyAmount
      (fun x => 2 ^ exponent x)
      (enlargedProjectedCandidateBlock C exponent)
      T := by
  rw [← longCycle_doubleCovered_card_eq_sum_pairOverlaps
    C exponent T hgirth]
  exact longCycle_doubleCovered_eq_totalSlack_add_deficiency
    C exponent hexpLt hexp honeLoss
    hdef hgirth


theorem coreDoubleCoveredWords_subset_coreUnion
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (T : Finset V) :
    coreDoubleCoveredWords C exponent T ⊆
      T.biUnion (enlargedProjectedCandidateBlock C exponent) := by
  intro word hdouble
  have hcard :=
    (mem_coreDoubleCoveredWords
      C exponent T word).1 hdouble
  have hpos :
      0 < (coreEnlargedCandidateFibre
        C exponent T word).card := by
    omega
  exact (mem_core_union_iff_fibre_nonempty
    C exponent T word).2
    (Finset.card_pos.mp hpos)

theorem longCycle_two_mul_pairOverlaps_le_sum_block_cards
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (T : Finset V)
    (hgirth :
      3 < (enlargedCollisionGraph C exponent T).girth) :
    2 *
      (∑ uv ∈ coreOrderedVertexPairs T,
        (corePairOverlapWords C exponent uv).card)
      ≤
    ∑ v ∈ T,
      (enlargedProjectedCandidateBlock
        C exponent v).card := by
  have hpair :=
    longCycle_doubleCovered_card_eq_sum_pairOverlaps
      C exponent T hgirth
  have hcount :=
    longCycle_sum_block_cards_eq_union_add_double
      C exponent T hgirth
  have hsub :=
    Finset.card_le_card
      (coreDoubleCoveredWords_subset_coreUnion
        C exponent T)
  rw [← hpair] 
  omega

theorem strict_enlargedBlock_card_le_two_mul_localSlack
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    {v : V}
    (hstrict : exponent v < projectedFree C v) :
    (enlargedProjectedCandidateBlock C exponent v).card
      ≤
    2 *
      (
        (enlargedProjectedCandidateBlock C exponent v).card -
          2 ^ exponent v
      ) := by
  have hnonloss :
      v ∉ projectedLossVertices C exponent := by
    intro hloss
    have heq :=
      (mem_projectedLossVertices C exponent v).1 hloss
    omega
  rw [enlargedProjectedCandidateBlock_nonloss
      C exponent hnonloss]
  have hcube :=
    retainedCompletionWords_card_le_two_mul_surplus_of_strict
      C exponent hstrict
  rw [retainedCompletionWords_card] at hcube ⊢
  unfold dyadicProfileSurplus at hcube
  exact hcube

theorem longCycle_exists_nonstrict_vertex
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
    (hgirth :
      3 < (enlargedCollisionGraph C exponent T).girth) :
    ∃ v ∈ T,
      ¬ exponent v < projectedFree C v := by
  classical
  by_contra hnone
  push_neg at hnone

  have hblockLe :
      (∑ v ∈ T,
        (enlargedProjectedCandidateBlock
          C exponent v).card)
        ≤
      2 *
        (∑ v ∈ T,
          (
            (enlargedProjectedCandidateBlock C exponent v).card -
              2 ^ exponent v
          )) := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro v hvT
    exact strict_enlargedBlock_card_le_two_mul_localSlack
      C exponent (hnone v hvT)

  have hedgeLe :=
    longCycle_two_mul_pairOverlaps_le_sum_block_cards
      C exponent T hgirth
  have hedgeEq :=
    longCycle_sum_pairOverlaps_eq_totalSlack_add_deficiency
      C exponent hexpLt hexp honeLoss
      hdef hgirth
  have hpos :=
    blockDeficiencyAmount_pos_of_deficient
      (fun x : V => 2 ^ exponent x)
      (enlargedProjectedCandidateBlock C exponent)
      hdef
  omega

theorem longCycle_exists_exact_or_loss_vertex
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
    (hgirth :
      3 < (enlargedCollisionGraph C exponent T).girth) :
    ∃ v ∈ T,
      ExactProjectedBudget C exponent v
      ∨
      v ∈ projectedLossVertices C exponent := by
  obtain ⟨v,hvT,hvNotStrict⟩ :=
    longCycle_exists_nonstrict_vertex
      C exponent hexpLt hexp honeLoss
      hdef hgirth
  rcases projectedProfile_strict_exact_or_loss
      C exponent hexp honeLoss v
    with hstrict | hexact | hloss
  · exact False.elim (hvNotStrict hstrict)
  · exact ⟨v,hvT,Or.inl hexact⟩
  · exact ⟨v,hvT,Or.inr hloss⟩


theorem lowerLoss_enlargedBlock_card_le_two_mul_localSlack
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    {v : V}
    (hvLoss : v ∈ projectedLossVertices C exponent)
    (hlower : exponent v + 2 ≤ n) :
    (enlargedProjectedCandidateBlock C exponent v).card
      ≤
    2 *
      (
        (enlargedProjectedCandidateBlock C exponent v).card -
          2 ^ exponent v
      ) := by
  have hactive :
      3 ≤ (retainedActive C v).card := by
    rw [projectedLoss_retainedActive_card
      C exponent hvLoss]
    omega
  have hblock :=
    allActiveLossCandidateBlock_card C v
  have hslack :=
    enlargedLoss_local_slack_eq_translated_minus_one_cube
      C exponent hvLoss
  rw [enlargedProjectedCandidateBlock_loss
      C exponent hvLoss]
  rw [hslack]
  rw [hblock]
  have hcoef :
      (retainedActive C v).card + 1
        ≤
      2 * ((retainedActive C v).card - 1) := by
    omega
  exact Nat.mul_le_mul_right
    (retainedCompletionWords C v).card hcoef

theorem longCycle_exists_exact_or_topLoss_vertex
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
    (hgirth :
      3 < (enlargedCollisionGraph C exponent T).girth) :
    ∃ v ∈ T,
      ExactProjectedBudget C exponent v
      ∨
      (
        v ∈ projectedLossVertices C exponent
        ∧ exponent v = n - 1
      ) := by
  classical
  by_contra hnone

  have hblockLe :
      (∑ v ∈ T,
        (enlargedProjectedCandidateBlock
          C exponent v).card)
        ≤
      2 *
        (∑ v ∈ T,
          (
            (enlargedProjectedCandidateBlock C exponent v).card -
              2 ^ exponent v
          )) := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro v hvT
    rcases projectedProfile_strict_exact_or_loss
        C exponent hexp honeLoss v
      with hstrict | hexact | hloss
    · exact strict_enlargedBlock_card_le_two_mul_localSlack
        C exponent hstrict
    · exact False.elim
        (hnone ⟨v,hvT,Or.inl hexact⟩)
    · have hnotTop :
          exponent v ≠ n - 1 := by
        intro htop
        exact hnone
          ⟨v,hvT,Or.inr ⟨hloss,htop⟩⟩
      have hlower :
          exponent v + 2 ≤ n := by
        have hlt := hexpLt v
        omega
      exact lowerLoss_enlargedBlock_card_le_two_mul_localSlack
        C exponent hloss hlower

  have hedgeLe :=
    longCycle_two_mul_pairOverlaps_le_sum_block_cards
      C exponent T hgirth
  have hedgeEq :=
    longCycle_sum_pairOverlaps_eq_totalSlack_add_deficiency
      C exponent hexpLt hexp honeLoss
      hdef hgirth
  have hpos :=
    blockDeficiencyAmount_pos_of_deficient
      (fun x : V => 2 ^ exponent x)
      (enlargedProjectedCandidateBlock C exponent)
      hdef
  omega


noncomputable def longCycleHardCredit
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (v : V) : ℕ := by
  classical
  exact
    if ExactProjectedBudget C exponent v then
      2 ^ exponent v
    else if
      v ∈ projectedLossVertices C exponent ∧
        exponent v = n - 1
    then
      (retainedCompletionWords C v).card
    else 0

theorem enlargedBlock_card_le_two_slack_add_hardCredit
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexpLt : ∀ x, exponent x < n)
    (hexp : ∀ x, exponent x ≤ n)
    (honeLoss :
      ∀ x, (active C x).card ≤ n - exponent x + 1)
    (v : V) :
    (enlargedProjectedCandidateBlock C exponent v).card
      ≤
    2 *
      (
        (enlargedProjectedCandidateBlock C exponent v).card -
          2 ^ exponent v
      )
      +
    longCycleHardCredit C exponent v := by
  classical
  rcases projectedProfile_strict_exact_or_loss
      C exponent hexp honeLoss v
    with hstrict | hexact | hloss
  · have hcredit :
        longCycleHardCredit C exponent v = 0 := by
      unfold longCycleHardCredit
      have hnotExact :
          ¬ ExactProjectedBudget C exponent v := by
        intro h
        unfold ExactProjectedBudget at h
        omega
      have hnotTopLoss :
          ¬ (v ∈ projectedLossVertices C exponent ∧
              exponent v = n - 1) := by
        rintro ⟨hloss',_⟩
        have heq :=
          (mem_projectedLossVertices C exponent v).1 hloss'
        omega
      simp [hnotExact,hnotTopLoss]
    rw [hcredit]
    simpa using
      strict_enlargedBlock_card_le_two_mul_localSlack
        C exponent hstrict
  · have hnonloss :
        v ∉ projectedLossVertices C exponent := by
      intro hloss'
      have heq :=
        (mem_projectedLossVertices C exponent v).1 hloss'
      unfold ExactProjectedBudget at hexact
      omega
    have hblock :
        (enlargedProjectedCandidateBlock C exponent v).card =
          2 ^ exponent v := by
      rw [enlargedProjectedCandidateBlock_nonloss
          C exponent hnonloss,
        retainedCompletionWords_card,
        hexact]
    have hcredit :
        longCycleHardCredit C exponent v =
          2 ^ exponent v := by
      unfold longCycleHardCredit
      simp [hexact]
    rw [hblock,hcredit]
    simp
  · by_cases htop : exponent v = n - 1
    · have hcredit :
          longCycleHardCredit C exponent v =
            (retainedCompletionWords C v).card := by
        unfold longCycleHardCredit
        have hnotExact :
            ¬ ExactProjectedBudget C exponent v := by
          intro h
          unfold ExactProjectedBudget at h
          have heq :=
            (mem_projectedLossVertices C exponent v).1 hloss
          omega
        simp [hnotExact,hloss,htop]
      have hactive :
          (retainedActive C v).card = 2 := by
        rw [projectedLoss_retainedActive_card
          C exponent hloss, htop]
        have hlt := hexpLt v
        omega
      have hblock :
          (enlargedProjectedCandidateBlock C exponent v).card =
            3 * (retainedCompletionWords C v).card := by
        rw [enlargedProjectedCandidateBlock_loss
            C exponent hloss,
          allActiveLossCandidateBlock_card,
          hactive]
      have hslack :=
        enlargedLoss_local_slack_eq_translated_minus_one_cube
          C exponent hloss
      rw [hcredit,hblock,hslack,hactive]
      omega
    · have hlower :
          exponent v + 2 ≤ n := by
        have hlt := hexpLt v
        omega
      have hcredit :
          longCycleHardCredit C exponent v = 0 := by
        unfold longCycleHardCredit
        have hnotExact :
            ¬ ExactProjectedBudget C exponent v := by
          intro h
          unfold ExactProjectedBudget at h
          have heq :=
            (mem_projectedLossVertices C exponent v).1 hloss
          omega
        simp [hnotExact,hloss,htop]
      rw [hcredit]
      simpa using
        lowerLoss_enlargedBlock_card_le_two_mul_localSlack
          C exponent hloss hlower

theorem longCycle_two_mul_deficiency_le_totalHardCredit
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
    (hgirth :
      3 < (enlargedCollisionGraph C exponent T).girth) :
    2 *
      blockDeficiencyAmount
        (fun x => 2 ^ exponent x)
        (enlargedProjectedCandidateBlock C exponent)
        T
      ≤
    ∑ v ∈ T,
      longCycleHardCredit C exponent v := by
  classical
  have hblocks :
      (∑ v ∈ T,
        (enlargedProjectedCandidateBlock C exponent v).card)
        ≤
      2 *
        (∑ v ∈ T,
          (
            (enlargedProjectedCandidateBlock C exponent v).card -
              2 ^ exponent v
          ))
        +
      ∑ v ∈ T,
        longCycleHardCredit C exponent v := by
    calc
      (∑ v ∈ T,
        (enlargedProjectedCandidateBlock C exponent v).card)
        ≤
      ∑ v ∈ T,
        (
          2 *
            (
              (enlargedProjectedCandidateBlock C exponent v).card -
                2 ^ exponent v
            )
          +
          longCycleHardCredit C exponent v
        ) := by
          apply Finset.sum_le_sum
          intro v hvT
          exact enlargedBlock_card_le_two_slack_add_hardCredit
            C exponent hexpLt hexp honeLoss v
      _ =
      2 *
        (∑ v ∈ T,
          (
            (enlargedProjectedCandidateBlock C exponent v).card -
              2 ^ exponent v
          ))
        +
      ∑ v ∈ T,
        longCycleHardCredit C exponent v := by
          rw [Finset.sum_add_distrib, Finset.mul_sum]

  have hedgeLe :=
    longCycle_two_mul_pairOverlaps_le_sum_block_cards
      C exponent T hgirth
  have hedgeEq :=
    longCycle_sum_pairOverlaps_eq_totalSlack_add_deficiency
      C exponent hexpLt hexp honeLoss
      hdef hgirth
  omega


theorem longCycle_core_card_ge_four
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    {T : Finset V}
    (hgirth :
      3 < (enlargedCollisionGraph C exponent T).girth) :
    4 ≤ T.card := by
  classical
  let G := enlargedCollisionGraph C exponent T
  have hcyclic : ¬ G.IsAcyclic := by
    intro hacyclic
    have hzero := hacyclic.girth_eq_zero
    dsimp [G] at hzero
    omega
  obtain ⟨a,p,hcycle,hgirthEq⟩ :=
    (SimpleGraph.exists_girth_eq_length
      (G := G)).2 hcyclic
  have hpLen : 4 ≤ p.length := by
    dsimp [G] at hgirthEq
    omega
  have htailPath : p.tail.IsPath :=
    hcycle.isPath_tail
  have htailLt :
      p.tail.length < Fintype.card {x : V // x ∈ T} :=
    htailPath.length_lt
  have htailLen :
      p.tail.length + 1 = p.length := by
    exact SimpleGraph.Walk.length_tail_add_one hcycle.not_nil
  have hcardSubtype :
      4 ≤ Fintype.card {x : V // x ∈ T} := by
    omega
  simpa only [Fintype.card_coe] using hcardSubtype

theorem topLoss_completion_card_current
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    {v : V}
    (hvLoss : v ∈ projectedLossVertices C exponent)
    (hvTop : exponent v = n - 1) :
    (retainedCompletionWords C v).card = 2 ^ (n - 2) := by
  rw [retainedCompletionWords_card]
  have hloss :=
    (mem_projectedLossVertices C exponent v).1 hvLoss
  unfold projectedFree at hloss
  have hact :
      (retainedActive C v).card ≤ n := by
    simpa using Finset.card_le_univ (retainedActive C v)
  have hfree :
      n - (retainedActive C v).card = n - 2 := by
    omega
  rw [hfree]

theorem topLoss_enlargedBlock_card_current
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    {v : V}
    (hvLoss : v ∈ projectedLossVertices C exponent)
    (hvTop : exponent v = n - 1) :
    (enlargedProjectedCandidateBlock C exponent v).card =
      3 * 2 ^ (n - 2) := by
  rw [enlargedProjectedCandidateBlock_loss
        C exponent hvLoss,
      allActiveLossCandidateBlock_card,
      projectedLoss_retainedActive_card
        C exponent hvLoss,
      topLoss_completion_card_current
        C exponent hvLoss hvTop]
  have hn2 : 2 ≤ n := by
    have hloss :=
      (mem_projectedLossVertices C exponent v).1 hvLoss
    unfold projectedFree at hloss
    omega
  omega

theorem two_topLoss_enlargedBlocks_union_eq_univ
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexp : ∀ x, exponent x ≤ n)
    (honeLoss :
      ∀ x, (active C x).card ≤ n - exponent x + 1)
    {u v : V}
    (huLoss : u ∈ projectedLossVertices C exponent)
    (hvLoss : v ∈ projectedLossVertices C exponent)
    (huv : u ≠ v)
    (huTop : exponent u = n - 1)
    (hvTop : exponent v = n - 1) :
    enlargedProjectedCandidateBlock C exponent u ∪
        enlargedProjectedCandidateBlock C exponent v
      =
    (Finset.univ : Finset (Fin n → Bool)) := by
  classical
  have hn2 : 2 ≤ n := by
    have huEq :=
      (mem_projectedLossVertices C exponent u).1 huLoss
    unfold projectedFree at huEq
    omega
  have hqU :=
    topLoss_completion_card_current
      C exponent huLoss huTop
  have hqV :=
    topLoss_completion_card_current
      C exponent hvLoss hvTop
  have hblockU :=
    topLoss_enlargedBlock_card_current
      C exponent huLoss huTop
  have hblockV :=
    topLoss_enlargedBlock_card_current
      C exponent hvLoss hvTop
  have hinter :=
    loss_allActive_pair_intersection_card_le_sum_cubes
      C exponent hexp honeLoss
      huLoss hvLoss huv
  rw [enlargedProjectedCandidateBlock_loss
        C exponent huLoss,
      enlargedProjectedCandidateBlock_loss
        C exponent hvLoss,
      hqU,hqV] at hinter
  have hambient :
      (enlargedProjectedCandidateBlock C exponent u ∪
        enlargedProjectedCandidateBlock C exponent v).card
        ≤ 2 ^ n := by
    have hsub :
        enlargedProjectedCandidateBlock C exponent u ∪
            enlargedProjectedCandidateBlock C exponent v
          ⊆
        (Finset.univ : Finset (Fin n → Bool)) :=
      Finset.subset_univ _
    simpa only [Finset.card_univ, Fintype.card_fun,
      Fintype.card_fin, Fintype.card_bool] using
      Finset.card_le_card hsub
  rw [Finset.card_union,hblockU,hblockV] at hambient
  have hpowN :
      2 ^ n = 4 * 2 ^ (n - 2) := by
    have hs : n - 2 + 2 = n := by omega
    calc
      2 ^ n = 2 ^ (n - 2 + 2) := by rw [hs]
      _ = 2 ^ (n - 2) * 2 ^ 2 := by rw [pow_add]
      _ = 4 * 2 ^ (n - 2) := by ring
  rw [hpowN] at hambient
  have hinterEq :
      (enlargedProjectedCandidateBlock C exponent u ∩
        enlargedProjectedCandidateBlock C exponent v).card
        =
      2 * 2 ^ (n - 2) := by
    omega
  apply Finset.eq_univ_of_card
  rw [Finset.card_union,hblockU,hblockV,hinterEq]
  simp only [Finset.card_univ, Fintype.card_fun,
    Fintype.card_fin, Fintype.card_bool]
  rw [hpowN]
  omega

theorem longCycle_at_most_one_topLoss
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
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
    (hgirth :
      3 < (enlargedCollisionGraph C exponent T).girth)
    {u v : V}
    (huT : u ∈ T)
    (hvT : v ∈ T)
    (huLoss : u ∈ projectedLossVertices C exponent)
    (hvLoss : v ∈ projectedLossVertices C exponent)
    (huTop : exponent u = n - 1)
    (hvTop : exponent v = n - 1) :
    u = v := by
  classical
  by_contra huv
  have hcover :=
    two_topLoss_enlargedBlocks_union_eq_univ
      C exponent hexp honeLoss
      huLoss hvLoss huv huTop hvTop
  have hcardT :
      4 ≤ T.card :=
    longCycle_core_card_ge_four
      C exponent hgirth
  have hpairSub :
      ({u,v} : Finset V) ⊆ T := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl
    · exact huT
    · exact hvT
  have hpairProper :
      ({u,v} : Finset V) ⊂ T := by
    refine ⟨hpairSub,?_⟩
    intro heq
    have hc := congrArg Finset.card heq
    simp [huv] at hc
    omega
  obtain ⟨w,hwT,hwNotPair⟩ :=
    Finset.exists_of_ssubset hpairProper
  have hwu : w ≠ u := by
    intro h
    subst w
    exact hwNotPair (by simp)
  have hwv : w ≠ v := by
    intro h
    subst w
    exact hwNotPair (by simp)
  let U : Finset V := {u,v,w}
  have hUSub : U ⊆ T := by
    intro x hx
    simp only [U, Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl
    · exact huT
    · exact hvT
    · exact hwT
  have hUCard : U.card = 3 := by
    simp [U,huv,hwu,hwv]
  have hUProper : U ⊂ T := by
    refine ⟨hUSub,?_⟩
    intro heq
    have hc := congrArg Finset.card heq
    rw [hUCard] at hc
    omega
  have hUUnion :
      U.biUnion
          (enlargedProjectedCandidateBlock C exponent)
        =
      (Finset.univ : Finset (Fin n → Bool)) := by
    ext word
    constructor
    · intro hword
      exact Finset.mem_univ _
    · intro _hword
      have hpairWord :
          word ∈ enlargedProjectedCandidateBlock C exponent u ∪
            enlargedProjectedCandidateBlock C exponent v := by
        rw [hcover]
        exact Finset.mem_univ _
      rcases Finset.mem_union.mp hpairWord with huWord | hvWord
      · apply Finset.mem_biUnion.mpr
        exact ⟨u,by simp [U],huWord⟩
      · apply Finset.mem_biUnion.mpr
        exact ⟨v,by simp [U],hvWord⟩
  have hUDef :
      BlockDeficient
        (fun x => 2 ^ exponent x)
        (enlargedProjectedCandidateBlock C exponent)
        U := by
    unfold BlockDeficient
    rw [hUUnion]
    have hsum :
        (∑ x ∈ U, 2 ^ exponent x)
          =
        2 ^ exponent u + 2 ^ exponent v +
          2 ^ exponent w := by
      simp [U,huv,hwu,hwv,add_assoc]
    rw [hsum,huTop,hvTop]
    simp only [Finset.card_univ, Fintype.card_fun,
      Fintype.card_fin, Fintype.card_bool]
    have hn1 : 1 ≤ n := by
      have huEq :=
        (mem_projectedLossVertices C exponent u).1 huLoss
      unfold projectedFree at huEq
      omega
    have hpow :
        2 ^ n = 2 * 2 ^ (n - 1) := by
      have hs : n - 1 + 1 = n := by omega
      calc
        2 ^ n = 2 ^ (n - 1 + 1) := by rw [hs]
        _ = 2 ^ (n - 1) * 2 := by rw [pow_succ]
        _ = 2 * 2 ^ (n - 1) := by omega
    rw [hpow]
    have hwPos : 0 < 2 ^ exponent w := by positivity
    omega
  exact (hmin U hUProper) hUDef


theorem longCycleHardCredit_eq_zero_of_not_exact_not_topLoss
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    {v : V}
    (hnotExact : ¬ ExactProjectedBudget C exponent v)
    (hnotTopLoss :
      ¬ (v ∈ projectedLossVertices C exponent ∧
          exponent v = n - 1)) :
    longCycleHardCredit C exponent v = 0 := by
  unfold longCycleHardCredit
  simp [hnotExact,hnotTopLoss]

theorem longCycle_noExact_totalHardCredit_le_topCube
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
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
    (hgirth :
      3 < (enlargedCollisionGraph C exponent T).girth)
    (hnoExact :
      ∀ v ∈ T, ¬ ExactProjectedBudget C exponent v)
    {top : V}
    (htopT : top ∈ T)
    (htopLoss : top ∈ projectedLossVertices C exponent)
    (htopExp : exponent top = n - 1) :
    (∑ v ∈ T, longCycleHardCredit C exponent v)
      ≤
    (retainedCompletionWords C top).card := by
  classical
  have htopCredit :
      longCycleHardCredit C exponent top =
        (retainedCompletionWords C top).card := by
    unfold longCycleHardCredit
    simp [hnoExact top htopT,htopLoss,htopExp]
  calc
    (∑ v ∈ T, longCycleHardCredit C exponent v)
      =
    longCycleHardCredit C exponent top +
      ∑ v ∈ T.erase top,
        longCycleHardCredit C exponent v := by
      rw [← Finset.sum_erase_add _ _ htopT]
      omega
    _ =
    longCycleHardCredit C exponent top := by
      have hzero :
          ∀ v ∈ T.erase top,
            longCycleHardCredit C exponent v = 0 := by
        intro v hvErase
        have hvT := (Finset.mem_erase.mp hvErase).2
        have hvNe := (Finset.mem_erase.mp hvErase).1
        have hnotTop :
            ¬ (v ∈ projectedLossVertices C exponent ∧
                exponent v = n - 1) := by
          rintro ⟨hvLoss,hvExp⟩
          have heq :=
            longCycle_at_most_one_topLoss
              C exponent hexp honeLoss
              hdef hmin hgirth
              hvT htopT hvLoss htopLoss
              hvExp htopExp
          exact hvNe heq
        have hz :=
          longCycleHardCredit_eq_zero_of_not_exact_not_topLoss
            C exponent
            (hnoExact v hvT) hnotTop
        rw [Finset.sum_eq_zero fun v hv => hzero v hv]
        simp
    _ =
    (retainedCompletionWords C top).card := htopCredit

theorem longCycle_noExact_two_mul_deficiency_le_topCube
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
    (hgirth :
      3 < (enlargedCollisionGraph C exponent T).girth)
    (hnoExact :
      ∀ v ∈ T, ¬ ExactProjectedBudget C exponent v)
    {top : V}
    (htopT : top ∈ T)
    (htopLoss : top ∈ projectedLossVertices C exponent)
    (htopExp : exponent top = n - 1) :
    2 *
      blockDeficiencyAmount
        (fun x => 2 ^ exponent x)
        (enlargedProjectedCandidateBlock C exponent)
        T
      ≤
    (retainedCompletionWords C top).card := by
  exact
    (longCycle_two_mul_deficiency_le_totalHardCredit
      C exponent hexpLt hexp honeLoss hdef hgirth).trans
      (longCycle_noExact_totalHardCredit_le_topCube
        C exponent hexp honeLoss
        hdef hmin hgirth hnoExact
        htopT htopLoss htopExp)

theorem longCycle_exact_or_singleTopLoss_lowDefect
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
    (hgirth :
      3 < (enlargedCollisionGraph C exponent T).girth) :
    (
      ∃ v ∈ T, ExactProjectedBudget C exponent v
    )
    ∨
    (
      ∃ top ∈ T,
        top ∈ projectedLossVertices C exponent ∧
        exponent top = n - 1 ∧
        2 *
          blockDeficiencyAmount
            (fun x => 2 ^ exponent x)
            (enlargedProjectedCandidateBlock C exponent)
            T
          ≤
        (retainedCompletionWords C top).card
    ) := by
  classical
  by_cases hexact :
      ∃ v ∈ T, ExactProjectedBudget C exponent v
  · exact Or.inl hexact
  · right
    have hnoExact :
        ∀ v ∈ T, ¬ ExactProjectedBudget C exponent v := by
      intro v hvT hvExact
      exact hexact ⟨v,hvT,hvExact⟩
    obtain ⟨top,htopT,htopHard⟩ :=
      longCycle_exists_exact_or_topLoss_vertex
        C exponent hexpLt hexp honeLoss
        hdef hgirth
    rcases htopHard with htopExact | ⟨htopLoss,htopExp⟩
    · exact False.elim
        (hnoExact top htopT htopExact)
    · exact ⟨top,htopT,htopLoss,htopExp,
        longCycle_noExact_two_mul_deficiency_le_topCube
          C exponent hexpLt hexp honeLoss
          hdef hmin hgirth hnoExact
          htopT htopLoss htopExp⟩


theorem topLoss_retainedActive_card_eq_two
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    {v : V}
    (hvLoss : v ∈ projectedLossVertices C exponent)
    (hvTop : exponent v = n - 1) :
    (retainedActive C v).card = 2 := by
  rw [projectedLoss_retainedActive_card
    C exponent hvLoss, hvTop]
  have hn2 : 2 ≤ n := by
    have heq :=
      (mem_projectedLossVertices C exponent v).1 hvLoss
    unfold projectedFree at heq
    omega
  omega

theorem topLoss_exists_two_distinct_active
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    {v : V}
    (hvLoss : v ∈ projectedLossVertices C exponent)
    (hvTop : exponent v = n - 1) :
    ∃ c d : Fin n,
      c ∈ retainedActive C v ∧
      d ∈ retainedActive C v ∧
      c ≠ d := by
  classical
  have hcard :=
    topLoss_retainedActive_card_eq_two
      C exponent hvLoss hvTop
  obtain ⟨c,d,hcd,hEq⟩ :=
    Finset.card_eq_two.mp hcard
  refine ⟨c,d,?_,?_,hcd⟩
  · rw [hEq]
    simp
  · rw [hEq]
    simp

theorem topLoss_word_five_exit_outlet
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexpLt : ∀ x, exponent x < n)
    (hexp : ∀ x, exponent x ≤ n)
    (honeLoss :
      ∀ x, (active C x).card ≤ n - exponent x + 1)
    {v : V}
    (hvLoss : v ∈ projectedLossVertices C exponent)
    (hvTop : exponent v = n - 1)
    {word : Fin n → Bool}
    (hword : word ∈ retainedCompletionWords C v) :
    (
      ∃ e : Fin n,
        e ∈ retainedActive C v ∧
        flipBoolWordAt word e ∉ coveredCompletionWords C
    )
    ∨
    (
      ∃ w : V,
        1 ≤ dyadicProfileSurplus
          exponent (projectedFree C) w
    )
    ∨
    (
      ∃ w : V,
        ExactProjectedBudget C exponent w
    )
    ∨
    (
      ∃ w : V,
        w ∈ projectedLossVertices C exponent ∧
        exponent w + 1 ≤ n - 1
    )
    ∨
    (
      ∃ w z : V,
        w ≠ z ∧
        w ∈ projectedLossVertices C exponent ∧
        z ∈ projectedLossVertices C exponent ∧
        exponent w = n - 1 ∧
        exponent z = n - 1
    ) := by
  classical
  obtain ⟨c,d,hc,hd,hcd⟩ :=
    topLoss_exists_two_distinct_active
      C exponent hvLoss hvTop
  rcases
    projectedLoss_two_exit_hole_or_paid_or_disjoint_exact_loss_fibres
      C exponent hexp honeLoss
      hvLoss hword hc hd hcd
    with hcHole | hdHole | hpaid | hhard
  · exact Or.inl ⟨c,hc,hcHole⟩
  · exact Or.inl ⟨d,hd,hdHole⟩
  · exact Or.inr (Or.inl
      ⟨hpaid.choose,hpaid.choose_spec.2⟩)
  · obtain ⟨hcNonempty,hdNonempty,_hcCard,_hdCard,hdisj,hprofile⟩ :=
      hhard
    by_cases hexact :
        ∃ w : V,
          (
            w ∈ completionFibre C (flipBoolWordAt word c)
            ∨
            w ∈ completionFibre C (flipBoolWordAt word d)
          ) ∧
          ExactProjectedBudget C exponent w
    · obtain ⟨w,_hwF,hwExact⟩ := hexact
      exact Or.inr (Or.inr (Or.inl ⟨w,hwExact⟩))
    · by_cases hlower :
        ∃ w : V,
          (
            w ∈ completionFibre C (flipBoolWordAt word c)
            ∨
            w ∈ completionFibre C (flipBoolWordAt word d)
          ) ∧
          w ∈ projectedLossVertices C exponent ∧
          exponent w + 1 ≤ n - 1
      · obtain ⟨w,_hwF,hwLoss,hwLower⟩ := hlower
        exact Or.inr (Or.inr (Or.inr
          (Or.inl ⟨w,hwLoss,hwLower⟩)))
      · have hallTop :
          ∀ w : V,
            (
              w ∈ completionFibre C (flipBoolWordAt word c)
              ∨
              w ∈ completionFibre C (flipBoolWordAt word d)
            ) →
            w ∈ projectedLossVertices C exponent ∧
            exponent w = n - 1 := by
          intro w hwF
          have hwProfile := hprofile w hwF
          rcases hwProfile.2 with hwExact | hwLoss
          · exact False.elim
              (hexact ⟨w,hwF,hwExact⟩)
          · refine ⟨hwLoss,?_⟩
            have hwLt := hexpLt w
            by_contra hnotTop
            have hwLower : exponent w + 1 ≤ n - 1 := by
              omega
            exact hlower ⟨w,hwF,hwLoss,hwLower⟩
        obtain ⟨w,hwc⟩ := hcNonempty
        obtain ⟨z,hzd⟩ := hdNonempty
        have hwTop := hallTop w (Or.inl hwc)
        have hzTop := hallTop z (Or.inr hzd)
        have hwz : w ≠ z := by
          intro h
          subst z
          exact Finset.disjoint_left.mp hdisj hwc hzd
        exact Or.inr (Or.inr (Or.inr
          (Or.inr ⟨w,z,hwz,
            hwTop.1,hzTop.1,hwTop.2,hzTop.2⟩)))



theorem topLoss_word_five_exit_outlet_with_lower_witness
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexpLt : ∀ x, exponent x < n)
    (hexp : ∀ x, exponent x ≤ n)
    (honeLoss :
      ∀ x, (active C x).card ≤ n - exponent x + 1)
    {v : V}
    (hvLoss : v ∈ projectedLossVertices C exponent)
    (hvTop : exponent v = n - 1)
    {word : Fin n → Bool}
    (hword : word ∈ retainedCompletionWords C v) :
    (
      ∃ e : Fin n,
        e ∈ retainedActive C v ∧
        flipBoolWordAt word e ∉ coveredCompletionWords C
    )
    ∨
    (
      ∃ w : V,
        1 ≤ dyadicProfileSurplus
          exponent (projectedFree C) w
    )
    ∨
    (
      ∃ w : V,
        ExactProjectedBudget C exponent w
    )
    ∨
    (
      ∃ w : V,
        w ∈ projectedLossVertices C exponent ∧
        exponent w + 1 ≤ n - 1 ∧
        ∃ e : Fin n,
          e ∈ retainedActive C v ∧
          flipBoolWordAt word e ∈ retainedCompletionWords C w
    )
    ∨
    (
      ∃ w z : V,
        w ≠ z ∧
        w ∈ projectedLossVertices C exponent ∧
        z ∈ projectedLossVertices C exponent ∧
        exponent w = n - 1 ∧
        exponent z = n - 1
    ) := by
  classical
  obtain ⟨c,d,hc,hd,hcd⟩ :=
    topLoss_exists_two_distinct_active
      C exponent hvLoss hvTop
  rcases
    projectedLoss_two_exit_hole_or_paid_or_disjoint_exact_loss_fibres
      C exponent hexp honeLoss
      hvLoss hword hc hd hcd
    with hcHole | hdHole | hpaid | hhard
  · exact Or.inl ⟨c,hc,hcHole⟩
  · exact Or.inl ⟨d,hd,hdHole⟩
  · exact Or.inr (Or.inl
      ⟨hpaid.choose,hpaid.choose_spec.2⟩)
  · obtain ⟨hcNonempty,hdNonempty,_hcCard,_hdCard,hdisj,hprofile⟩ :=
      hhard
    by_cases hexact :
        ∃ w : V,
          (
            w ∈ completionFibre C (flipBoolWordAt word c)
            ∨
            w ∈ completionFibre C (flipBoolWordAt word d)
          ) ∧
          ExactProjectedBudget C exponent w
    · obtain ⟨w,_hwF,hwExact⟩ := hexact
      exact Or.inr (Or.inr (Or.inl ⟨w,hwExact⟩))
    · by_cases hlower :
        ∃ w : V,
          (
            w ∈ completionFibre C (flipBoolWordAt word c)
            ∨
            w ∈ completionFibre C (flipBoolWordAt word d)
          ) ∧
          w ∈ projectedLossVertices C exponent ∧
          exponent w + 1 ≤ n - 1
      · obtain ⟨w,hwF,hwLoss,hwLower⟩ := hlower
        rcases hwF with hwc | hwd
        · exact Or.inr (Or.inr (Or.inr
            (Or.inl ⟨w,hwLoss,hwLower,
              c,hc,
              (mem_completionFibre
                C (flipBoolWordAt word c) w).1 hwc⟩)))
        · exact Or.inr (Or.inr (Or.inr
            (Or.inl ⟨w,hwLoss,hwLower,
              d,hd,
              (mem_completionFibre
                C (flipBoolWordAt word d) w).1 hwd⟩)))
      · have hallTop :
          ∀ w : V,
            (
              w ∈ completionFibre C (flipBoolWordAt word c)
              ∨
              w ∈ completionFibre C (flipBoolWordAt word d)
            ) →
            w ∈ projectedLossVertices C exponent ∧
            exponent w = n - 1 := by
          intro w hwF
          have hwProfile := hprofile w hwF
          rcases hwProfile.2 with hwExact | hwLoss
          · exact False.elim
              (hexact ⟨w,hwF,hwExact⟩)
          · refine ⟨hwLoss,?_⟩
            have hwLt := hexpLt w
            by_contra hnotTop
            have hwLower : exponent w + 1 ≤ n - 1 := by
              omega
            exact hlower ⟨w,hwF,hwLoss,hwLower⟩
        obtain ⟨w,hwc⟩ := hcNonempty
        obtain ⟨z,hzd⟩ := hdNonempty
        have hwTop := hallTop w (Or.inl hwc)
        have hzTop := hallTop z (Or.inr hzd)
        have hwz : w ≠ z := by
          intro h
          subst z
          exact Finset.disjoint_left.mp hdisj hwc hzd
        exact Or.inr (Or.inr (Or.inr
          (Or.inr ⟨w,z,hwz,
            hwTop.1,hzTop.1,hwTop.2,hzTop.2⟩)))

#print axioms topLoss_word_five_exit_outlet_with_lower_witness

theorem deepLoss_enlargedBlock_add_cube_le_two_mul_localSlack
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    {v : V}
    (hvLoss : v ∈ projectedLossVertices C exponent)
    (hdeep : exponent v + 3 ≤ n) :
    (enlargedProjectedCandidateBlock C exponent v).card +
        (retainedCompletionWords C v).card
      ≤
    2 *
      (
        (enlargedProjectedCandidateBlock C exponent v).card -
          2 ^ exponent v
      ) := by
  have hactive :
      4 ≤ (retainedActive C v).card := by
    rw [projectedLoss_retainedActive_card
      C exponent hvLoss]
    omega
  have hblock :=
    allActiveLossCandidateBlock_card C v
  have hslack :=
    enlargedLoss_local_slack_eq_translated_minus_one_cube
      C exponent hvLoss
  rw [enlargedProjectedCandidateBlock_loss
      C exponent hvLoss]
  rw [hslack,hblock]
  have hcoef :
      (retainedActive C v).card + 2
        ≤
      2 * ((retainedActive C v).card - 1) := by
    omega
  exact Nat.mul_le_mul_right
    (retainedCompletionWords C v).card hcoef

theorem lowerLoss_secondLayer_or_deep
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    {v : V}
    (hvLoss : v ∈ projectedLossVertices C exponent)
    (hexpLt : exponent v < n)
    (hlower : exponent v + 1 ≤ n - 1) :
    exponent v = n - 2
    ∨
    exponent v + 3 ≤ n := by
  omega

#print axioms deepLoss_enlargedBlock_add_cube_le_two_mul_localSlack
#print axioms lowerLoss_secondLayer_or_deep

end OrderedEdgeColoring
end JSP000404Research
