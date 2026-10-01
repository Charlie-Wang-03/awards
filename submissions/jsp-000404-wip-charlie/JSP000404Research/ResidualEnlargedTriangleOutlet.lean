import JSP000404Research.ResidualEnlargedCollisionSimpleGraph
import JSP000404Research.ResidualExactSharedRecursiveOutlet
import JSP000404Research.ResidualLossCycleLocal
import Mathlib.Tactic

/-!
# Structured outlet for collision triangles

A raw triangle in the enlarged collision graph is too weak as a recursive
obstruction: it does not record where projected loss occurs.

The existing triangle-loss classification gives exactly two meaningful
possibilities.

* At least two triangle vertices are projected-loss.
* Exactly one vertex is projected-loss; then the edge joining the two
  non-loss vertices is necessarily a residual edge.

This file packages that dichotomy as a small inductive outlet suitable for the
planar root reduction.  No geometric information is discarded.
-/

namespace JSP000404Research
namespace OrderedEdgeColoring

inductive EnlargedTriangleOutlet
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (T : Finset V)
    (u v w : {x : V // x ∈ T}) : Prop
  | twoLossUV
      (huLoss : u.1 ∈ projectedLossVertices C exponent)
      (hvLoss : v.1 ∈ projectedLossVertices C exponent)
  | twoLossUW
      (huLoss : u.1 ∈ projectedLossVertices C exponent)
      (hwLoss : w.1 ∈ projectedLossVertices C exponent)
  | twoLossVW
      (hvLoss : v.1 ∈ projectedLossVertices C exponent)
      (hwLoss : w.1 ∈ projectedLossVertices C exponent)
  | oneLossUResidual
      (huLoss : u.1 ∈ projectedLossVertices C exponent)
      (hvNonloss : v.1 ∉ projectedLossVertices C exponent)
      (hwNonloss : w.1 ∉ projectedLossVertices C exponent)
      (hres :
        (v.1 < w.1 ∧ IsResidual C v.1 w.1)
        ∨
        (w.1 < v.1 ∧ IsResidual C w.1 v.1))
  | oneLossVResidual
      (hvLoss : v.1 ∈ projectedLossVertices C exponent)
      (huNonloss : u.1 ∉ projectedLossVertices C exponent)
      (hwNonloss : w.1 ∉ projectedLossVertices C exponent)
      (hres :
        (u.1 < w.1 ∧ IsResidual C u.1 w.1)
        ∨
        (w.1 < u.1 ∧ IsResidual C w.1 u.1))
  | oneLossWResidual
      (hwLoss : w.1 ∈ projectedLossVertices C exponent)
      (huNonloss : u.1 ∉ projectedLossVertices C exponent)
      (hvNonloss : v.1 ∉ projectedLossVertices C exponent)
      (hres :
        (u.1 < v.1 ∧ IsResidual C u.1 v.1)
        ∨
        (v.1 < u.1 ∧ IsResidual C v.1 u.1))

theorem enlargedCollisionGraph_triangle_outlet
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexp : ∀ x, exponent x ≤ n)
    (honeLoss :
      ∀ x, (active C x).card ≤ n - exponent x + 1)
    (T : Finset V)
    {u v w : {x : V // x ∈ T}}
    (huv :
      (enlargedCollisionGraph C exponent T).Adj u v)
    (huw :
      (enlargedCollisionGraph C exponent T).Adj u w)
    (hvw :
      (enlargedCollisionGraph C exponent T).Adj v w) :
    EnlargedTriangleOutlet C exponent T u v w := by
  rcases
    enlargedCollisionGraph_triangle_loss_shape
      C exponent T huv huw hvw
    with hU | hV | hW | hUV | hUW | hVW
  · exact EnlargedTriangleOutlet.oneLossUResidual
      hU.huLoss hU.hvNonloss hU.hwNonloss
      (enlargedTriangle_oneLoss_has_nonloss_residual_edge
        C exponent hexp honeLoss T
        huv huw hvw
        hU.huLoss hU.hvNonloss hU.hwNonloss)
  · exact EnlargedTriangleOutlet.oneLossVResidual
      hV.hvLoss hV.huNonloss hV.hwNonloss
      (enlargedTriangle_oneLoss_has_nonloss_residual_edge
        C exponent hexp honeLoss T
        huv.symm hvw huw
        hV.hvLoss hV.huNonloss hV.hwNonloss)
  · exact EnlargedTriangleOutlet.oneLossWResidual
      hW.hwLoss hW.huNonloss hW.hvNonloss
      (enlargedTriangle_oneLoss_has_nonloss_residual_edge
        C exponent hexp honeLoss T
        huw.symm hvw.symm huv
        hW.hwLoss hW.huNonloss hW.hvNonloss)
  · exact EnlargedTriangleOutlet.twoLossUV
      hUV.huLoss hUV.hvLoss
  · exact EnlargedTriangleOutlet.twoLossUW
      hUW.huLoss hUW.hwLoss
  · exact EnlargedTriangleOutlet.twoLossVW
      hVW.hvLoss hVW.hwLoss

#print axioms enlargedCollisionGraph_triangle_outlet


/-- A collision edge between two non-loss vertices is already closed by the
profile trichotomy: a strict endpoint pays positive surplus, while an
exact--exact pair enters the existing exact recursive outlet. -/
theorem enlargedTriangle_nonloss_edge_paid_or_exactRecursive
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexp : ∀ x, exponent x ≤ n)
    (honeLoss :
      ∀ x, (active C x).card ≤ n - exponent x + 1)
    (T : Finset V)
    {u v : {x : V // x ∈ T}}
    (huv :
      (enlargedCollisionGraph C exponent T).Adj u v)
    (huNonloss : u.1 ∉ projectedLossVertices C exponent)
    (hvNonloss : v.1 ∉ projectedLossVertices C exponent) :
    (
      ∃ w : V,
        1 ≤ dyadicProfileSurplus
          exponent (projectedFree C) w
    )
    ∨
    (
      ∃ source : V,
        ExactRecursiveOutlet C exponent source
    ) := by
  have hcross :=
    enlargedCollisionGraph_cross_of_adj
      C exponent T huv
  obtain ⟨word,huBlock,hvBlock⟩ := hcross
  have huWord :
      word ∈ retainedCompletionWords C u.1 := by
    rw [enlargedProjectedCandidateBlock_nonloss
      C exponent huNonloss] at huBlock
    exact huBlock
  have hvWord :
      word ∈ retainedCompletionWords C v.1 := by
    rw [enlargedProjectedCandidateBlock_nonloss
      C exponent hvNonloss] at hvBlock
    exact hvBlock
  have huvNe : u.1 ≠ v.1 := by
    intro h
    apply (enlargedCollisionGraph C exponent T).ne_of_adj huv
    apply Subtype.ext
    exact h
  rcases projectedProfile_strict_exact_or_loss
      C exponent hexp honeLoss u.1
    with huStrict | huExact | huLoss
  · exact Or.inl
      ⟨u.1,
        projected_strict_surplus_at_least_one
          exponent (projectedFree C) huStrict⟩
  · rcases projectedProfile_strict_exact_or_loss
        C exponent hexp honeLoss v.1
      with hvStrict | hvExact | hvLoss
    · exact Or.inl
        ⟨v.1,
          projected_strict_surplus_at_least_one
            exponent (projectedFree C) hvStrict⟩
    · have hout :
          ExactSharedOutlet C exponent u.1 :=
        ExactSharedOutlet.exactPair
          v.1 huvNe hvExact word huWord hvWord
      exact Or.inr
        ⟨u.1,
          exactSharedOutlet_to_recursive
            C exponent huExact hout⟩
    · exact False.elim (hvNonloss hvLoss)
  · exact False.elim (huNonloss huLoss)

/-- Every enlarged collision triangle is therefore either already paid /
recursive, or its genuinely hard remainder contains two projected-loss
vertices. -/
theorem enlargedCollisionGraph_triangle_twoLoss_or_paid_or_exactRecursive
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexp : ∀ x, exponent x ≤ n)
    (honeLoss :
      ∀ x, (active C x).card ≤ n - exponent x + 1)
    (T : Finset V)
    {u v w : {x : V // x ∈ T}}
    (huv :
      (enlargedCollisionGraph C exponent T).Adj u v)
    (huw :
      (enlargedCollisionGraph C exponent T).Adj u w)
    (hvw :
      (enlargedCollisionGraph C exponent T).Adj v w) :
    (
      ∃ a b : {x : V // x ∈ T},
        a ≠ b ∧
        a.1 ∈ projectedLossVertices C exponent ∧
        b.1 ∈ projectedLossVertices C exponent
    )
    ∨
    (
      ∃ z : V,
        1 ≤ dyadicProfileSurplus
          exponent (projectedFree C) z
    )
    ∨
    (
      ∃ source : V,
        ExactRecursiveOutlet C exponent source
    ) := by
  rcases
    enlargedCollisionGraph_triangle_loss_shape
      C exponent T huv huw hvw
    with hU | hV | hW | hUV | hUW | hVW
  · rcases
      enlargedTriangle_nonloss_edge_paid_or_exactRecursive
        C exponent hexp honeLoss T
        hvw hU.hvNonloss hU.hwNonloss
      with hpaid | hrec
    · exact Or.inr (Or.inl hpaid)
    · exact Or.inr (Or.inr hrec)
  · rcases
      enlargedTriangle_nonloss_edge_paid_or_exactRecursive
        C exponent hexp honeLoss T
        huw hV.huNonloss hV.hwNonloss
      with hpaid | hrec
    · exact Or.inr (Or.inl hpaid)
    · exact Or.inr (Or.inr hrec)
  · rcases
      enlargedTriangle_nonloss_edge_paid_or_exactRecursive
        C exponent hexp honeLoss T
        huv hW.huNonloss hW.hvNonloss
      with hpaid | hrec
    · exact Or.inr (Or.inl hpaid)
    · exact Or.inr (Or.inr hrec)
  · exact Or.inl
      ⟨u,v,
        (enlargedCollisionGraph C exponent T).ne_of_adj huv,
        hUV.huLoss,hUV.hvLoss⟩
  · exact Or.inl
      ⟨u,w,
        (enlargedCollisionGraph C exponent T).ne_of_adj huw,
        hUW.huLoss,hUW.hwLoss⟩
  · exact Or.inl
      ⟨v,w,
        (enlargedCollisionGraph C exponent T).ne_of_adj hvw,
        hVW.hvLoss,hVW.hwLoss⟩

#print axioms enlargedTriangle_nonloss_edge_paid_or_exactRecursive
#print axioms enlargedCollisionGraph_triangle_twoLoss_or_paid_or_exactRecursive


/-- Two distinct projected-loss vertices which are not already deep can only
occupy the top or second exponent layers.  Since the top layer has global
multiplicity at most one, the hard pair has one of exactly three layer
patterns: top--second, second--top, or second--second. -/
theorem two_projectedLoss_highLayer_classification
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexpLt : ∀ x, exponent x < n)
    (htop :
      ((Finset.univ : Finset V).filter
        (fun z => exponent z = n - 1)).card ≤ 1)
    {u v : V}
    (huv : u ≠ v)
    (huLoss : u ∈ projectedLossVertices C exponent)
    (hvLoss : v ∈ projectedLossVertices C exponent) :
    (
      exponent u + 3 ≤ n
    )
    ∨
    (
      exponent v + 3 ≤ n
    )
    ∨
    (
      exponent u = n - 1 ∧ exponent v = n - 2
    )
    ∨
    (
      exponent u = n - 2 ∧ exponent v = n - 1
    )
    ∨
    (
      exponent u = n - 2 ∧ exponent v = n - 2
    ) := by
  classical
  by_cases huDeep : exponent u + 3 ≤ n
  · exact Or.inl huDeep
  · right
    by_cases hvDeep : exponent v + 3 ≤ n
    · exact Or.inl hvDeep
    · right
      have huLayer :
          exponent u = n - 1 ∨ exponent u = n - 2 := by
        have huLt := hexpLt u
        omega
      have hvLayer :
          exponent v = n - 1 ∨ exponent v = n - 2 := by
        have hvLt := hexpLt v
        omega
      rcases huLayer with huTop | huSecond
      · rcases hvLayer with hvTop | hvSecond
        · exfalso
          have huMem :
              u ∈ (Finset.univ : Finset V).filter
                (fun z => exponent z = n - 1) := by
            simp [huTop]
          have hvMem :
              v ∈ (Finset.univ : Finset V).filter
                (fun z => exponent z = n - 1) := by
            simp [hvTop]
          exact huv (Finset.card_le_one.mp htop huMem hvMem)
        · exact Or.inl ⟨huTop,hvSecond⟩
      · rcases hvLayer with hvTop | hvSecond
        · exact Or.inr (Or.inl ⟨huSecond,hvTop⟩)
        · exact Or.inr (Or.inr ⟨huSecond,hvSecond⟩)

/-- Consequently the genuinely hard two-loss branch of a collision triangle
is reduced to a finite high-layer pair classification. -/
theorem enlargedCollisionGraph_triangle_highLayerLossPair_or_paid_or_exactRecursive
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
      (enlargedCollisionGraph C exponent T).Adj v w) :
    (
      ∃ a b : {x : V // x ∈ T},
        a ≠ b ∧
        a.1 ∈ projectedLossVertices C exponent ∧
        b.1 ∈ projectedLossVertices C exponent ∧
        (
          exponent a.1 + 3 ≤ n
          ∨
          exponent b.1 + 3 ≤ n
          ∨
          (exponent a.1 = n - 1 ∧ exponent b.1 = n - 2)
          ∨
          (exponent a.1 = n - 2 ∧ exponent b.1 = n - 1)
          ∨
          (exponent a.1 = n - 2 ∧ exponent b.1 = n - 2)
        )
    )
    ∨
    (
      ∃ z : V,
        1 ≤ dyadicProfileSurplus
          exponent (projectedFree C) z
    )
    ∨
    (
      ∃ source : V,
        ExactRecursiveOutlet C exponent source
    ) := by
  rcases
    enlargedCollisionGraph_triangle_twoLoss_or_paid_or_exactRecursive
      C exponent hexp honeLoss T huv huw hvw
    with hlossPair | hpaid | hrec
  · obtain ⟨a,b,hab,haLoss,hbLoss⟩ := hlossPair
    exact Or.inl
      ⟨a,b,hab,haLoss,hbLoss,
        two_projectedLoss_highLayer_classification
          C exponent hexpLt htop
          (by
            intro h
            apply hab
            apply Subtype.ext
            exact h)
          haLoss hbLoss⟩
  · exact Or.inr (Or.inl hpaid)
  · exact Or.inr (Or.inr hrec)

#print axioms two_projectedLoss_highLayer_classification
#print axioms enlargedCollisionGraph_triangle_highLayerLossPair_or_paid_or_exactRecursive


/-- Root-ready form of the triangle reduction: deep loss is exported
immediately, while the only unresolved triangle branch is a distinct
high-layer loss pair of type top--second, second--top, or second--second. -/
theorem enlargedCollisionGraph_triangle_deep_or_highPair_or_paid_or_exactRecursive
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
      (enlargedCollisionGraph C exponent T).Adj v w) :
    (
      ∃ z : V,
        z ∈ projectedLossVertices C exponent ∧
        exponent z + 3 ≤ n
    )
    ∨
    (
      ∃ a b : {x : V // x ∈ T},
        a ≠ b ∧
        a.1 ∈ projectedLossVertices C exponent ∧
        b.1 ∈ projectedLossVertices C exponent ∧
        (
          (exponent a.1 = n - 1 ∧ exponent b.1 = n - 2)
          ∨
          (exponent a.1 = n - 2 ∧ exponent b.1 = n - 1)
          ∨
          (exponent a.1 = n - 2 ∧ exponent b.1 = n - 2)
        )
    )
    ∨
    (
      ∃ z : V,
        1 ≤ dyadicProfileSurplus
          exponent (projectedFree C) z
    )
    ∨
    (
      ∃ source : V,
        ExactRecursiveOutlet C exponent source
    ) := by
  rcases
    enlargedCollisionGraph_triangle_highLayerLossPair_or_paid_or_exactRecursive
      C exponent hexpLt hexp honeLoss htop T huv huw hvw
    with hlossPair | hpaid | hrec
  · obtain ⟨a,b,hab,haLoss,hbLoss,hcases⟩ := hlossPair
    rcases hcases with haDeep | hbDeep | haTopSecond | haSecondTop | hbothSecond
    · exact Or.inl ⟨a.1,haLoss,haDeep⟩
    · exact Or.inl ⟨b.1,hbLoss,hbDeep⟩
    · exact Or.inr (Or.inl
        ⟨a,b,hab,haLoss,hbLoss,Or.inl haTopSecond⟩)
    · exact Or.inr (Or.inl
        ⟨a,b,hab,haLoss,hbLoss,Or.inr (Or.inl haSecondTop)⟩)
    · exact Or.inr (Or.inl
        ⟨a,b,hab,haLoss,hbLoss,Or.inr (Or.inr hbothSecond)⟩)
  · exact Or.inr (Or.inr (Or.inl hpaid))
  · exact Or.inr (Or.inr (Or.inr hrec))

#print axioms enlargedCollisionGraph_triangle_deep_or_highPair_or_paid_or_exactRecursive


/-- At an ordered triangle's middle projected-loss vertex, the two incident
edge colours are retained, active, and distinct.  In the top layer these two
coordinates exhaust the active-cardinality budget. -/
theorem topLoss_middle_triangle_palette_card_two
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexp : ∀ x, exponent x ≤ n)
    (honeLoss :
      ∀ x, (active C x).card ≤ n - exponent x + 1)
    {a b c : V}
    (hab : a < b)
    (hbc : b < c)
    (hbLoss : b ∈ projectedLossVertices C exponent)
    (hbTop : exponent b = n - 1) :
    let hleft :=
      projectedLoss_edge_left_retained
        C exponent hexp honeLoss hbLoss hab
    let hright :=
      projectedLoss_edge_right_retained
        C exponent hexp honeLoss hbLoss hbc
    let cleft := retainedColor C a b hleft
    let cright := retainedColor C b c hright
    cleft ∈ retainedActive C b ∧
    cright ∈ retainedActive C b ∧
    cleft ≠ cright ∧
    (retainedActive C b).card = 2 := by
  dsimp
  let hleft :=
    projectedLoss_edge_left_retained
      C exponent hexp honeLoss hbLoss hab
  let hright :=
    projectedLoss_edge_right_retained
      C exponent hexp honeLoss hbLoss hbc
  have hleftActive :
      retainedColor C a b hleft ∈ retainedActive C b :=
    retainedColor_mem_retainedActive_right C hab hleft
  have hrightActive :
      retainedColor C b c hright ∈ retainedActive C b :=
    retainedColor_mem_retainedActive_left C hbc hright
  have hne :
      retainedColor C a b hleft ≠
        retainedColor C b c hright :=
    projectedLoss_two_sided_retained_colours_ne
      C exponent hexp honeLoss hbLoss hab hbc
  have hcard :
      (retainedActive C b).card = 2 := by
    rw [projectedLoss_retainedActive_card C exponent hbLoss, hbTop]
    have hn2 : 2 ≤ n := by
      have hloss :=
        (mem_projectedLossVertices C exponent b).1 hbLoss
      unfold projectedFree at hloss
      omega
    omega
  exact ⟨hleftActive,hrightActive,hne,hcard⟩

/-- The corresponding second-layer middle loss vertex has the same two
distinct incident active coordinates and active-cardinality exactly three.
Hence downstream arguments have exactly one further active-coordinate slot
beyond the two triangle directions. -/
theorem secondLayerLoss_middle_triangle_palette_card_three
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexp : ∀ x, exponent x ≤ n)
    (honeLoss :
      ∀ x, (active C x).card ≤ n - exponent x + 1)
    {a b c : V}
    (hab : a < b)
    (hbc : b < c)
    (hbLoss : b ∈ projectedLossVertices C exponent)
    (hbSecond : exponent b = n - 2) :
    let hleft :=
      projectedLoss_edge_left_retained
        C exponent hexp honeLoss hbLoss hab
    let hright :=
      projectedLoss_edge_right_retained
        C exponent hexp honeLoss hbLoss hbc
    let cleft := retainedColor C a b hleft
    let cright := retainedColor C b c hright
    cleft ∈ retainedActive C b ∧
    cright ∈ retainedActive C b ∧
    cleft ≠ cright ∧
    (retainedActive C b).card = 3 := by
  dsimp
  let hleft :=
    projectedLoss_edge_left_retained
      C exponent hexp honeLoss hbLoss hab
  let hright :=
    projectedLoss_edge_right_retained
      C exponent hexp honeLoss hbLoss hbc
  have hleftActive :
      retainedColor C a b hleft ∈ retainedActive C b :=
    retainedColor_mem_retainedActive_right C hab hleft
  have hrightActive :
      retainedColor C b c hright ∈ retainedActive C b :=
    retainedColor_mem_retainedActive_left C hbc hright
  have hne :
      retainedColor C a b hleft ≠
        retainedColor C b c hright :=
    projectedLoss_two_sided_retained_colours_ne
      C exponent hexp honeLoss hbLoss hab hbc
  have hcard :
      (retainedActive C b).card = 3 :=
    secondLayerLoss_retainedActive_card_eq_three
      C exponent hbLoss hbSecond
  exact ⟨hleftActive,hrightActive,hne,hcard⟩

#print axioms topLoss_middle_triangle_palette_card_two
#print axioms secondLayerLoss_middle_triangle_palette_card_three


/-- Away from genuine triple coverage, the two pair-overlap sets incident to a
triangle vertex are disjoint.  Thus a triangle differs from the long-cycle
counting regime precisely when one Boolean word is carried by all three
candidate blocks. -/
theorem triangle_incident_overlaps_disjoint_of_no_triple_word
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    {u v w : V}
    (hnoTriple :
      ¬ ∃ word : Fin n → Bool,
        word ∈ enlargedProjectedCandidateBlock C exponent u ∧
        word ∈ enlargedProjectedCandidateBlock C exponent v ∧
        word ∈ enlargedProjectedCandidateBlock C exponent w) :
    Disjoint
      (enlargedProjectedCandidateBlock C exponent u ∩
        enlargedProjectedCandidateBlock C exponent v)
      (enlargedProjectedCandidateBlock C exponent u ∩
        enlargedProjectedCandidateBlock C exponent w) := by
  classical
  rw [Finset.disjoint_left]
  intro word huv huw
  have huvParts := Finset.mem_inter.mp huv
  have huwParts := Finset.mem_inter.mp huw
  exact hnoTriple
    ⟨word,huvParts.1,huvParts.2,huwParts.2⟩

/-- Conversely, failure of incident pair-overlap disjointness produces an
explicit triple-covered Boolean word. -/
theorem triangle_triple_word_of_incident_overlaps_not_disjoint
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    {u v w : V}
    (hnot :
      ¬ Disjoint
        (enlargedProjectedCandidateBlock C exponent u ∩
          enlargedProjectedCandidateBlock C exponent v)
        (enlargedProjectedCandidateBlock C exponent u ∩
          enlargedProjectedCandidateBlock C exponent w)) :
    ∃ word : Fin n → Bool,
      word ∈ enlargedProjectedCandidateBlock C exponent u ∧
      word ∈ enlargedProjectedCandidateBlock C exponent v ∧
      word ∈ enlargedProjectedCandidateBlock C exponent w := by
  by_contra hno
  exact hnot
    (triangle_incident_overlaps_disjoint_of_no_triple_word
      C exponent hno)

/-- For three distinct projected-loss vertices, a common enlarged-block word
must be translated at at least two vertices.  Those two translations
necessarily use different retained coordinates. -/
theorem three_loss_triple_word_has_cross_translated_pair
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexp : ∀ x, exponent x ≤ n)
    (honeLoss :
      ∀ x, (active C x).card ≤ n - exponent x + 1)
    {u v w : V}
    (huv : u ≠ v)
    (huw : u ≠ w)
    (hvw : v ≠ w)
    (huLoss : u ∈ projectedLossVertices C exponent)
    (hvLoss : v ∈ projectedLossVertices C exponent)
    (hwLoss : w ∈ projectedLossVertices C exponent)
    {word : Fin n → Bool}
    (huBlock : word ∈ enlargedProjectedCandidateBlock C exponent u)
    (hvBlock : word ∈ enlargedProjectedCandidateBlock C exponent v)
    (hwBlock : word ∈ enlargedProjectedCandidateBlock C exponent w) :
    (
      ∃ c d : Fin n,
        c ∈ retainedActive C u ∧
        d ∈ retainedActive C v ∧
        c ≠ d ∧
        word ∈ translatedCompletionWords C u c ∧
        word ∈ translatedCompletionWords C v d
    )
    ∨
    (
      ∃ c d : Fin n,
        c ∈ retainedActive C u ∧
        d ∈ retainedActive C w ∧
        c ≠ d ∧
        word ∈ translatedCompletionWords C u c ∧
        word ∈ translatedCompletionWords C w d
    )
    ∨
    (
      ∃ c d : Fin n,
        c ∈ retainedActive C v ∧
        d ∈ retainedActive C w ∧
        c ≠ d ∧
        word ∈ translatedCompletionWords C v c ∧
        word ∈ translatedCompletionWords C w d
    ) := by
  classical
  rw [enlargedProjectedCandidateBlock_loss
        C exponent huLoss] at huBlock
  rw [enlargedProjectedCandidateBlock_loss
        C exponent hvLoss] at hvBlock
  rw [enlargedProjectedCandidateBlock_loss
        C exponent hwLoss] at hwBlock
  unfold allActiveLossCandidateBlock at huBlock hvBlock hwBlock
  rcases Finset.mem_union.mp huBlock with huQ | huT
  · rcases Finset.mem_union.mp hvBlock with hvQ | hvT
    · exact False.elim
        (Finset.disjoint_left.mp
          (projectedLoss_completion_disjoint
            C exponent hexp honeLoss huLoss huv)
          huQ hvQ)
    · rcases Finset.mem_union.mp hwBlock with hwQ | hwT
      · exact False.elim
          (Finset.disjoint_left.mp
            (projectedLoss_completion_disjoint
              C exponent hexp honeLoss huLoss huw)
            huQ hwQ)
      · obtain ⟨cv,hcv,hvWord⟩ :=
          Finset.mem_biUnion.mp hvT
        obtain ⟨cw,hcw,hwWord⟩ :=
          Finset.mem_biUnion.mp hwT
        have hne :=
          translated_loss_conflict_distinct_coordinates
            C exponent hexp honeLoss
            hvLoss hwLoss hvw
            ⟨word,hvWord,hwWord⟩
        exact Or.inr (Or.inr
          ⟨cv,cw,hcv,hcw,hne,hvWord,hwWord⟩)
  · obtain ⟨cu,hcu,huWord⟩ :=
      Finset.mem_biUnion.mp huT
    rcases Finset.mem_union.mp hvBlock with hvQ | hvT
    · rcases Finset.mem_union.mp hwBlock with hwQ | hwT
      · exact False.elim
          (Finset.disjoint_left.mp
            (projectedLoss_completion_disjoint
              C exponent hexp honeLoss hvLoss hvw)
            hvQ hwQ)
      · obtain ⟨cw,hcw,hwWord⟩ :=
          Finset.mem_biUnion.mp hwT
        have hne :=
          translated_loss_conflict_distinct_coordinates
            C exponent hexp honeLoss
            huLoss hwLoss huw
            ⟨word,huWord,hwWord⟩
        exact Or.inr
          (Or.inl ⟨cu,cw,hcu,hcw,hne,huWord,hwWord⟩)
    · obtain ⟨cv,hcv,hvWord⟩ :=
        Finset.mem_biUnion.mp hvT
      have hne :=
        translated_loss_conflict_distinct_coordinates
          C exponent hexp honeLoss
          huLoss hvLoss huv
          ⟨word,huWord,hvWord⟩
      exact Or.inl
        ⟨cu,cv,hcu,hcv,hne,huWord,hvWord⟩

#print axioms triangle_incident_overlaps_disjoint_of_no_triple_word
#print axioms triangle_triple_word_of_incident_overlaps_not_disjoint
#print axioms three_loss_triple_word_has_cross_translated_pair


/-- A genuine cross-translated loss pair inherits the monotone owner-bit
constraint from the translated-loss fibre theory. -/
theorem cross_translated_loss_pair_ordered_bit_semantics
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexp : ∀ x, exponent x ≤ n)
    (honeLoss :
      ∀ x, (active C x).card ≤ n - exponent x + 1)
    {x y : V}
    (hxy : x ≠ y)
    (hxLoss : x ∈ projectedLossVertices C exponent)
    (hyLoss : y ∈ projectedLossVertices C exponent)
    {word : Fin n → Bool}
    {cx cy : Fin n}
    (hcx : cx ∈ retainedActive C x)
    (hcy : cy ∈ retainedActive C y)
    (hxWord : word ∈ translatedCompletionWords C x cx)
    (hyWord : word ∈ translatedCompletionWords C y cy) :
    (
      x < y ∧ (word cx = true ∨ word cy = false)
    )
    ∨
    (
      y < x ∧ (word cy = true ∨ word cx = false)
    ) := by
  rcases lt_or_gt_of_ne hxy with hlt | hgt
  · exact Or.inl
      ⟨hlt,
        translated_loss_fibre_no_false_before_true
          C exponent hexp honeLoss hlt
          hxLoss hyLoss hcx hcy hxWord hyWord⟩
  · exact Or.inr
      ⟨hgt,
        translated_loss_fibre_no_false_before_true
          C exponent hexp honeLoss hgt
          hyLoss hxLoss hcy hcx hyWord hxWord⟩

/-- Therefore every triple-covered word of three distinct loss vertices
contains an ordered cross-translated carrier pair satisfying the fibre
monotonicity bit constraint. -/
theorem three_loss_triple_word_has_ordered_monotone_cross_pair
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexp : ∀ x, exponent x ≤ n)
    (honeLoss :
      ∀ x, (active C x).card ≤ n - exponent x + 1)
    {u v w : V}
    (huv : u ≠ v)
    (huw : u ≠ w)
    (hvw : v ≠ w)
    (huLoss : u ∈ projectedLossVertices C exponent)
    (hvLoss : v ∈ projectedLossVertices C exponent)
    (hwLoss : w ∈ projectedLossVertices C exponent)
    {word : Fin n → Bool}
    (huBlock : word ∈ enlargedProjectedCandidateBlock C exponent u)
    (hvBlock : word ∈ enlargedProjectedCandidateBlock C exponent v)
    (hwBlock : word ∈ enlargedProjectedCandidateBlock C exponent w) :
    (
      ∃ x y : V, ∃ cx cy : Fin n,
        x ≠ y ∧
        x ∈ projectedLossVertices C exponent ∧
        y ∈ projectedLossVertices C exponent ∧
        cx ∈ retainedActive C x ∧
        cy ∈ retainedActive C y ∧
        cx ≠ cy ∧
        word ∈ translatedCompletionWords C x cx ∧
        word ∈ translatedCompletionWords C y cy ∧
        (
          (x < y ∧ (word cx = true ∨ word cy = false))
          ∨
          (y < x ∧ (word cy = true ∨ word cx = false))
        )
    ) := by
  rcases
    three_loss_triple_word_has_cross_translated_pair
      C exponent hexp honeLoss
      huv huw hvw
      huLoss hvLoss hwLoss
      huBlock hvBlock hwBlock
    with huvT | huwT | hvwT
  · obtain ⟨cu,cv,hcu,hcv,hne,huWord,hvWord⟩ := huvT
    exact ⟨u,v,cu,cv,huv,huLoss,hvLoss,hcu,hcv,hne,
      huWord,hvWord,
      cross_translated_loss_pair_ordered_bit_semantics
        C exponent hexp honeLoss
        huv huLoss hvLoss hcu hcv huWord hvWord⟩
  · obtain ⟨cu,cw,hcu,hcw,hne,huWord,hwWord⟩ := huwT
    exact ⟨u,w,cu,cw,huw,huLoss,hwLoss,hcu,hcw,hne,
      huWord,hwWord,
      cross_translated_loss_pair_ordered_bit_semantics
        C exponent hexp honeLoss
        huw huLoss hwLoss hcu hcw huWord hwWord⟩
  · obtain ⟨cv,cw,hcv,hcw,hne,hvWord,hwWord⟩ := hvwT
    exact ⟨v,w,cv,cw,hvw,hvLoss,hwLoss,hcv,hcw,hne,
      hvWord,hwWord,
      cross_translated_loss_pair_ordered_bit_semantics
        C exponent hexp honeLoss
        hvw hvLoss hwLoss hcv hcw hvWord hwWord⟩

#print axioms cross_translated_loss_pair_ordered_bit_semantics
#print axioms three_loss_triple_word_has_ordered_monotone_cross_pair

end OrderedEdgeColoring
end JSP000404Research
