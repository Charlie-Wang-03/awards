import JSP000404Research.ResidualSecondLayerTripleCanonical
import Mathlib.Tactic

/-!
# Source-preserving Q/T/T canonicalization

The existing threeSecond_commonWord_QTT_or_closed theorem intentionally
forgets which of the original three carriers become the two translated owners.
For minimal-core arguments this provenance matters.

This file repeats only the final case split and preserves the exact fact that
the two translated owners x,y are two members of the original triple
{u,v,w}.  The completion owner s remains a blocker and need not belong to the
original triple.
-/

namespace JSP000404Research
namespace OrderedEdgeColoring

theorem threeSecond_commonWord_QTT_or_closed_with_sources
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexpLt : ∀ z, exponent z < n)
    (hexp : ∀ z, exponent z ≤ n)
    (honeLoss :
      ∀ z, (active C z).card ≤ n - exponent z + 1)
    {u v w : V}
    (huv : u ≠ v)
    (huw : u ≠ w)
    (hvw : v ≠ w)
    (huLoss : u ∈ projectedLossVertices C exponent)
    (hvLoss : v ∈ projectedLossVertices C exponent)
    (hwLoss : w ∈ projectedLossVertices C exponent)
    (huSecond : exponent u = n - 2)
    (hvSecond : exponent v = n - 2)
    (hwSecond : exponent w = n - 2)
    {word : Fin n → Bool}
    (huBlock : word ∈ enlargedProjectedCandidateBlock C exponent u)
    (hvBlock : word ∈ enlargedProjectedCandidateBlock C exponent v)
    (hwBlock : word ∈ enlargedProjectedCandidateBlock C exponent w) :
    (
      ∃ hole : Fin n → Bool,
        hole ∉ coveredCompletionWords C
    )
    ∨
    (
      ∃ z : V,
        1 ≤ dyadicProfileSurplus
          exponent (projectedFree C) z
    )
    ∨
    (
      ∃ z : V,
        ExactProjectedBudget C exponent z
    )
    ∨
    (
      ∃ z : V,
        z ∈ projectedLossVertices C exponent ∧
        exponent z = n - 1
    )
    ∨
    (
      ∃ z : V,
        z ∈ projectedLossVertices C exponent ∧
        exponent z + 3 ≤ n
    )
    ∨
    (
      ∃ s x y : V,
      ∃ cx cy : Fin n,
        s ≠ x ∧ s ≠ y ∧ x ≠ y ∧
        x ∈ ({u,v,w} : Finset V) ∧
        y ∈ ({u,v,w} : Finset V) ∧
        s ∈ projectedLossVertices C exponent ∧
        x ∈ projectedLossVertices C exponent ∧
        y ∈ projectedLossVertices C exponent ∧
        exponent s = n - 2 ∧
        exponent x = n - 2 ∧
        exponent y = n - 2 ∧
        cx ∈ retainedActive C x ∧
        cy ∈ retainedActive C y ∧
        cx ≠ cy ∧
        word ∈ retainedCompletionWords C s ∧
        word ∈ translatedCompletionWords C x cx ∧
        word ∈ translatedCompletionWords C y cy
    ) := by
  rcases
    three_loss_triple_word_has_cross_translated_pair
      C exponent hexp honeLoss
      huv huw hvw
      huLoss hvLoss hwLoss
      huBlock hvBlock hwBlock
    with huvT | huwT | hvwT
  · obtain ⟨cu,cv,hcu,hcv,hcuv,huT,hvT⟩ := huvT
    rcases
      secondLayer_translated_word_blocker_or_closed
        C exponent hexpLt hexp honeLoss
        huLoss huSecond hcu huT
      with hhole | hpaid | hexact | htop | hdeep | hblocker
    · exact Or.inl hhole
    · exact Or.inr (Or.inl hpaid)
    · exact Or.inr (Or.inr (Or.inl hexact))
    · exact Or.inr (Or.inr (Or.inr (Or.inl htop)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hdeep))))
    · obtain ⟨s,hsu,hsLoss,hsSecond,hsQ⟩ := hblocker
      have hsv : s ≠ v := by
        intro hsvEq
        subst s
        exact Finset.disjoint_left.mp
          (translatedCompletionWords_disjoint_original_of_active C hcv)
          hvT hsQ
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        ⟨s,u,v,cu,cv,
          hsu,hsv,huv,
          by simp,by simp,
          hsLoss,huLoss,hvLoss,
          hsSecond,huSecond,hvSecond,
          hcu,hcv,hcuv,hsQ,huT,hvT⟩))))
  · obtain ⟨cu,cw,hcu,hcw,hcuw,huT,hwT⟩ := huwT
    rcases
      secondLayer_translated_word_blocker_or_closed
        C exponent hexpLt hexp honeLoss
        huLoss huSecond hcu huT
      with hhole | hpaid | hexact | htop | hdeep | hblocker
    · exact Or.inl hhole
    · exact Or.inr (Or.inl hpaid)
    · exact Or.inr (Or.inr (Or.inl hexact))
    · exact Or.inr (Or.inr (Or.inr (Or.inl htop)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hdeep))))
    · obtain ⟨s,hsu,hsLoss,hsSecond,hsQ⟩ := hblocker
      have hsw : s ≠ w := by
        intro hswEq
        subst s
        exact Finset.disjoint_left.mp
          (translatedCompletionWords_disjoint_original_of_active C hcw)
          hwT hsQ
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        ⟨s,u,w,cu,cw,
          hsu,hsw,huw,
          by simp,by simp,
          hsLoss,huLoss,hwLoss,
          hsSecond,huSecond,hwSecond,
          hcu,hcw,hcuw,hsQ,huT,hwT⟩))))
  · obtain ⟨cv,cw,hcv,hcw,hcvw,hvT,hwT⟩ := hvwT
    rcases
      secondLayer_translated_word_blocker_or_closed
        C exponent hexpLt hexp honeLoss
        hvLoss hvSecond hcv hvT
      with hhole | hpaid | hexact | htop | hdeep | hblocker
    · exact Or.inl hhole
    · exact Or.inr (Or.inl hpaid)
    · exact Or.inr (Or.inr (Or.inl hexact))
    · exact Or.inr (Or.inr (Or.inr (Or.inl htop)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hdeep))))
    · obtain ⟨s,hsv,hsLoss,hsSecond,hsQ⟩ := hblocker
      have hsw : s ≠ w := by
        intro hswEq
        subst s
        exact Finset.disjoint_left.mp
          (translatedCompletionWords_disjoint_original_of_active C hcw)
          hwT hsQ
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        ⟨s,v,w,cv,cw,
          hsv,hsw,hvw,
          by simp,by simp,
          hsLoss,hvLoss,hwLoss,
          hsSecond,hvSecond,hwSecond,
          hcv,hcw,hcvw,hsQ,hvT,hwT⟩))))

#print axioms threeSecond_commonWord_QTT_or_closed_with_sources


/-- Source-preserving saturated upgrade.  In the hard branch the two original
translated owners remain certified members of the original triple {u,v,w};
only the completion owner s and the unique-third-exit blocker z may be fresh. -/
theorem threeSecond_commonWord_QTTT_or_closed_with_sources
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexpLt : ∀ z, exponent z < n)
    (hexp : ∀ z, exponent z ≤ n)
    (honeLoss :
      ∀ z, (active C z).card ≤ n - exponent z + 1)
    {u v w : V}
    (huv : u ≠ v)
    (huw : u ≠ w)
    (hvw : v ≠ w)
    (huLoss : u ∈ projectedLossVertices C exponent)
    (hvLoss : v ∈ projectedLossVertices C exponent)
    (hwLoss : w ∈ projectedLossVertices C exponent)
    (huSecond : exponent u = n - 2)
    (hvSecond : exponent v = n - 2)
    (hwSecond : exponent w = n - 2)
    {word : Fin n → Bool}
    (huBlock : word ∈ enlargedProjectedCandidateBlock C exponent u)
    (hvBlock : word ∈ enlargedProjectedCandidateBlock C exponent v)
    (hwBlock : word ∈ enlargedProjectedCandidateBlock C exponent w) :
    (
      ∃ hole : Fin n → Bool,
        hole ∉ coveredCompletionWords C
    )
    ∨
    (
      ∃ q : V,
        1 ≤ dyadicProfileSurplus
          exponent (projectedFree C) q
    )
    ∨
    (
      ∃ q : V,
        ExactProjectedBudget C exponent q
    )
    ∨
    (
      ∃ q : V,
        q ∈ projectedLossVertices C exponent ∧
        exponent q = n - 1
    )
    ∨
    (
      ∃ q : V,
        q ∈ projectedLossVertices C exponent ∧
        exponent q + 3 ≤ n
    )
    ∨
    (
      ∃ s x y z : V,
      ∃ cx cy cz : Fin n,
        s ≠ x ∧ s ≠ y ∧ s ≠ z ∧
        x ≠ y ∧ x ≠ z ∧ y ≠ z ∧
        x ∈ ({u,v,w} : Finset V) ∧
        y ∈ ({u,v,w} : Finset V) ∧
        s ∈ projectedLossVertices C exponent ∧
        x ∈ projectedLossVertices C exponent ∧
        y ∈ projectedLossVertices C exponent ∧
        z ∈ projectedLossVertices C exponent ∧
        exponent s = n - 2 ∧
        exponent x = n - 2 ∧
        exponent y = n - 2 ∧
        exponent z = n - 2 ∧
        cx ∈ retainedActive C x ∧
        cy ∈ retainedActive C y ∧
        cz ∈ retainedActive C z ∧
        cx ≠ cy ∧ cx ≠ cz ∧ cy ≠ cz ∧
        retainedActive C s = {cx,cy,cz} ∧
        word ∈ retainedCompletionWords C s ∧
        word ∈ translatedCompletionWords C x cx ∧
        word ∈ translatedCompletionWords C y cy ∧
        word ∈ translatedCompletionWords C z cz
    ) := by
  rcases
    threeSecond_commonWord_QTT_or_closed_with_sources
      C exponent hexpLt hexp honeLoss
      huv huw hvw
      huLoss hvLoss hwLoss
      huSecond hvSecond hwSecond
      huBlock hvBlock hwBlock
    with hhole | hpaid | hexact | htop | hdeep | hQTT
  · exact Or.inl hhole
  · exact Or.inr (Or.inl hpaid)
  · exact Or.inr (Or.inr (Or.inl hexact))
  · exact Or.inr (Or.inr (Or.inr (Or.inl htop)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hdeep))))
  · obtain ⟨s,x,y,cx,cy,
      hsx,hsy,hxy,hxSource,hySource,
      hsLoss,hxLoss,hyLoss,
      hsSecond,hxSecond,hySecond,
      hcx,hcy,hcxy,hsQ,hxT,hyT⟩ := hQTT
    rcases
      QTT_hard_branch_upgrades_to_QTTT
        C exponent hexpLt hexp honeLoss
        hsx hsy hxy
        hsLoss hxLoss hyLoss
        hsSecond hxSecond hySecond
        hcx hcy hcxy hsQ hxT hyT
      with hhole2 | hpaid2 | hexact2 | htop2 | hdeep2 | hQTTT
    · exact Or.inl hhole2
    · exact Or.inr (Or.inl hpaid2)
    · exact Or.inr (Or.inr (Or.inl hexact2))
    · exact Or.inr (Or.inr (Or.inr (Or.inl htop2)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hdeep2))))
    · obtain ⟨cz,z,hsz,hxz,hyz,
        hzLoss,hzSecond,
        _hcxS,_hcyS,_hczS,
        _hcxy2,hcxz,hcyz,hsActive,
        _hcxX,_hcyY,hczZ,
        _hsQ2,_hxT2,_hyT2,hzT⟩ := hQTTT
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        ⟨s,x,y,z,cx,cy,cz,
          hsx,hsy,hsz,hxy,hxz,hyz,
          hxSource,hySource,
          hsLoss,hxLoss,hyLoss,hzLoss,
          hsSecond,hxSecond,hySecond,hzSecond,
          hcx,hcy,hczZ,
          hcxy,hcxz,hcyz,hsActive,
          hsQ,hxT,hyT,hzT⟩))))

#print axioms threeSecond_commonWord_QTTT_or_closed_with_sources

end OrderedEdgeColoring
end JSP000404Research
