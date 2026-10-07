import JSP000404Research.ResidualEnlargedTriangleOutlet
import Mathlib.Tactic

/-!
# Common-word triangle reduction to the second layer

A triple-covered Boolean word gives three core vertices which are pairwise
adjacent in the enlarged collision graph.  The earlier triangle outlet keeps
only a hard two-loss pair and therefore discards the profile of the third
carrier.

For the planar endgame that loss is expensive: once a hard pair is
second--second, the third carrier decides whether we already have a standard
outlet or the three-second-layer common-word configuration needed by the
Q/T/T/T canonicalization.

This file preserves that information.  A common-word collision triangle is
reduced to exactly one of the following reusable states:

* paid surplus;
* exact recursive outlet;
* exact projected budget;
* deep projected loss;
* a top--second projected-loss pair, with the common word retained at both
  endpoints;
* three second-layer projected-loss carriers of the original common word.

No planar geometry is used here.
-/

namespace JSP000404Research
namespace OrderedEdgeColoring

inductive CommonWordTriangleSecondLayerOutlet
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (T : Finset V)
    (word : Fin n → Bool)
    (u v w : {x : V // x ∈ T}) : Prop
  | paid
      (z : V)
      (hz : 1 ≤ dyadicProfileSurplus exponent (projectedFree C) z)
  | exactRecursive
      (source : V)
      (hout : ExactRecursiveOutlet C exponent source)
  | exact
      (z : V)
      (hz : ExactProjectedBudget C exponent z)
  | deep
      (z : V)
      (hzLoss : z ∈ projectedLossVertices C exponent)
      (hzDeep : exponent z + 3 ≤ n)
  | topSecond
      (top second : {x : V // x ∈ T})
      (hne : top ≠ second)
      (htopLoss : top.1 ∈ projectedLossVertices C exponent)
      (hsecondLoss : second.1 ∈ projectedLossVertices C exponent)
      (htop : exponent top.1 = n - 1)
      (hsecond : exponent second.1 = n - 2)
      (htopWord :
        word ∈ enlargedProjectedCandidateBlock C exponent top.1)
      (hsecondWord :
        word ∈ enlargedProjectedCandidateBlock C exponent second.1)
  | threeSecond
      (huLoss : u.1 ∈ projectedLossVertices C exponent)
      (hvLoss : v.1 ∈ projectedLossVertices C exponent)
      (hwLoss : w.1 ∈ projectedLossVertices C exponent)
      (huSecond : exponent u.1 = n - 2)
      (hvSecond : exponent v.1 = n - 2)
      (hwSecond : exponent w.1 = n - 2)
      (huWord :
        word ∈ enlargedProjectedCandidateBlock C exponent u.1)
      (hvWord :
        word ∈ enlargedProjectedCandidateBlock C exponent v.1)
      (hwWord :
        word ∈ enlargedProjectedCandidateBlock C exponent w.1)

theorem enlargedCollisionGraph_commonWord_triangle_secondLayer_outlet
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexpLt : ∀ x, exponent x < n)
    (hexp : ∀ x, exponent x ≤ n)
    (honeLoss :
      ∀ x, (active C x).card ≤ n - exponent x + 1)
    (htop :
      ((Finset.univ : Finset V).filter
        (fun z => exponent z = n - 1)).card ≤ 1)
    (T : Finset V)
    {u v w : {x : V // x ∈ T}}
    (huv :
      (enlargedCollisionGraph C exponent T).Adj u v)
    (huw :
      (enlargedCollisionGraph C exponent T).Adj u w)
    (hvw :
      (enlargedCollisionGraph C exponent T).Adj v w)
    {word : Fin n → Bool}
    (huWord :
      word ∈ enlargedProjectedCandidateBlock C exponent u.1)
    (hvWord :
      word ∈ enlargedProjectedCandidateBlock C exponent v.1)
    (hwWord :
      word ∈ enlargedProjectedCandidateBlock C exponent w.1) :
    CommonWordTriangleSecondLayerOutlet
      C exponent T word u v w := by
  have huvVal : u.1 ≠ v.1 := by
    intro h
    exact (enlargedCollisionGraph C exponent T).ne_of_adj huv
      (Subtype.ext h)
  have huwVal : u.1 ≠ w.1 := by
    intro h
    exact (enlargedCollisionGraph C exponent T).ne_of_adj huw
      (Subtype.ext h)
  have hvwVal : v.1 ≠ w.1 := by
    intro h
    exact (enlargedCollisionGraph C exponent T).ne_of_adj hvw
      (Subtype.ext h)

  rcases
    enlargedCollisionGraph_triangle_loss_shape
      C exponent T huv huw hvw
    with hU | hV | hW | hUV | hUW | hVW
  · rcases
      enlargedTriangle_nonloss_edge_paid_or_exactRecursive
        C exponent hexp honeLoss T
        hvw hU.hvNonloss hU.hwNonloss
      with hpaid | hrec
    · obtain ⟨z,hz⟩ := hpaid
      exact CommonWordTriangleSecondLayerOutlet.paid z hz
    · obtain ⟨source,hout⟩ := hrec
      exact CommonWordTriangleSecondLayerOutlet.exactRecursive source hout
  · rcases
      enlargedTriangle_nonloss_edge_paid_or_exactRecursive
        C exponent hexp honeLoss T
        huw hV.huNonloss hV.hwNonloss
      with hpaid | hrec
    · obtain ⟨z,hz⟩ := hpaid
      exact CommonWordTriangleSecondLayerOutlet.paid z hz
    · obtain ⟨source,hout⟩ := hrec
      exact CommonWordTriangleSecondLayerOutlet.exactRecursive source hout
  · rcases
      enlargedTriangle_nonloss_edge_paid_or_exactRecursive
        C exponent hexp honeLoss T
        huv hW.huNonloss hW.hvNonloss
      with hpaid | hrec
    · obtain ⟨z,hz⟩ := hpaid
      exact CommonWordTriangleSecondLayerOutlet.paid z hz
    · obtain ⟨source,hout⟩ := hrec
      exact CommonWordTriangleSecondLayerOutlet.exactRecursive source hout

  · rcases
      two_projectedLoss_highLayer_classification
        C exponent hexpLt htop huvVal hUV.huLoss hUV.hvLoss
      with huDeep | hvDeep | huTopSecond | huSecondTop | huvSecond
    · exact CommonWordTriangleSecondLayerOutlet.deep
        u.1 hUV.huLoss huDeep
    · exact CommonWordTriangleSecondLayerOutlet.deep
        v.1 hUV.hvLoss hvDeep
    · exact CommonWordTriangleSecondLayerOutlet.topSecond
        u v (by exact (enlargedCollisionGraph C exponent T).ne_of_adj huv)
        hUV.huLoss hUV.hvLoss
        huTopSecond.1 huTopSecond.2 huWord hvWord
    · exact CommonWordTriangleSecondLayerOutlet.topSecond
        v u (by exact (enlargedCollisionGraph C exponent T).ne_of_adj huv.symm)
        hUV.hvLoss hUV.huLoss
        huSecondTop.2 huSecondTop.1 hvWord huWord
    · rcases projectedProfile_strict_exact_or_loss
          C exponent hexp honeLoss w.1
        with hwStrict | hwExact | hwLoss
      · exact CommonWordTriangleSecondLayerOutlet.paid
          w.1
          (projected_strict_surplus_at_least_one
            exponent (projectedFree C) hwStrict)
      · exact CommonWordTriangleSecondLayerOutlet.exact w.1 hwExact
      · rcases exponent_top_second_or_deep exponent (hexpLt w.1)
          with hwTop | hwSecond | hwDeep
        · exact CommonWordTriangleSecondLayerOutlet.topSecond
            w u
            (by exact (enlargedCollisionGraph C exponent T).ne_of_adj huw.symm)
            hwLoss hUV.huLoss
            hwTop huvSecond.1 hwWord huWord
        · exact CommonWordTriangleSecondLayerOutlet.threeSecond
            hUV.huLoss hUV.hvLoss hwLoss
            huvSecond.1 huvSecond.2 hwSecond
            huWord hvWord hwWord
        · exact CommonWordTriangleSecondLayerOutlet.deep
            w.1 hwLoss hwDeep

  · rcases
      two_projectedLoss_highLayer_classification
        C exponent hexpLt htop huwVal hUW.huLoss hUW.hwLoss
      with huDeep | hwDeep | huTopSecond | huSecondTop | huwSecond
    · exact CommonWordTriangleSecondLayerOutlet.deep
        u.1 hUW.huLoss huDeep
    · exact CommonWordTriangleSecondLayerOutlet.deep
        w.1 hUW.hwLoss hwDeep
    · exact CommonWordTriangleSecondLayerOutlet.topSecond
        u w (by exact (enlargedCollisionGraph C exponent T).ne_of_adj huw)
        hUW.huLoss hUW.hwLoss
        huTopSecond.1 huTopSecond.2 huWord hwWord
    · exact CommonWordTriangleSecondLayerOutlet.topSecond
        w u (by exact (enlargedCollisionGraph C exponent T).ne_of_adj huw.symm)
        hUW.hwLoss hUW.huLoss
        huSecondTop.2 huSecondTop.1 hwWord huWord
    · rcases projectedProfile_strict_exact_or_loss
          C exponent hexp honeLoss v.1
        with hvStrict | hvExact | hvLoss
      · exact CommonWordTriangleSecondLayerOutlet.paid
          v.1
          (projected_strict_surplus_at_least_one
            exponent (projectedFree C) hvStrict)
      · exact CommonWordTriangleSecondLayerOutlet.exact v.1 hvExact
      · rcases exponent_top_second_or_deep exponent (hexpLt v.1)
          with hvTop | hvSecond | hvDeep
        · exact CommonWordTriangleSecondLayerOutlet.topSecond
            v u
            (by exact (enlargedCollisionGraph C exponent T).ne_of_adj huv.symm)
            hvLoss hUW.huLoss
            hvTop huwSecond.1 hvWord huWord
        · exact CommonWordTriangleSecondLayerOutlet.threeSecond
            hUW.huLoss hvLoss hUW.hwLoss
            huwSecond.1 hvSecond huwSecond.2
            huWord hvWord hwWord
        · exact CommonWordTriangleSecondLayerOutlet.deep
            v.1 hvLoss hvDeep

  · rcases
      two_projectedLoss_highLayer_classification
        C exponent hexpLt htop hvwVal hVW.hvLoss hVW.hwLoss
      with hvDeep | hwDeep | hvTopSecond | hvSecondTop | hvwSecond
    · exact CommonWordTriangleSecondLayerOutlet.deep
        v.1 hVW.hvLoss hvDeep
    · exact CommonWordTriangleSecondLayerOutlet.deep
        w.1 hVW.hwLoss hwDeep
    · exact CommonWordTriangleSecondLayerOutlet.topSecond
        v w (by exact (enlargedCollisionGraph C exponent T).ne_of_adj hvw)
        hVW.hvLoss hVW.hwLoss
        hvTopSecond.1 hvTopSecond.2 hvWord hwWord
    · exact CommonWordTriangleSecondLayerOutlet.topSecond
        w v (by exact (enlargedCollisionGraph C exponent T).ne_of_adj hvw.symm)
        hVW.hwLoss hVW.hvLoss
        hvSecondTop.2 hvSecondTop.1 hwWord hvWord
    · rcases projectedProfile_strict_exact_or_loss
          C exponent hexp honeLoss u.1
        with huStrict | huExact | huLoss
      · exact CommonWordTriangleSecondLayerOutlet.paid
          u.1
          (projected_strict_surplus_at_least_one
            exponent (projectedFree C) huStrict)
      · exact CommonWordTriangleSecondLayerOutlet.exact u.1 huExact
      · rcases exponent_top_second_or_deep exponent (hexpLt u.1)
          with huTop | huSecond | huDeep
        · exact CommonWordTriangleSecondLayerOutlet.topSecond
            u v
            (by exact (enlargedCollisionGraph C exponent T).ne_of_adj huv)
            huLoss hVW.hvLoss
            huTop hvwSecond.1 huWord hvWord
        · exact CommonWordTriangleSecondLayerOutlet.threeSecond
            huLoss hVW.hvLoss hVW.hwLoss
            huSecond hvwSecond.1 hvwSecond.2
            huWord hvWord hwWord
        · exact CommonWordTriangleSecondLayerOutlet.deep
            u.1 huLoss huDeep

#print axioms enlargedCollisionGraph_commonWord_triangle_secondLayer_outlet

end OrderedEdgeColoring
end JSP000404Research
