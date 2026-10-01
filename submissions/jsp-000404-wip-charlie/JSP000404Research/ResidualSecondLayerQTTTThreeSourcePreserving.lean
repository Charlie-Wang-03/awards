import JSP000404Research.ResidualQTTTThirdSourcePreserving
import JSP000404Research.ResidualSecondLayerQTTCoreMembership
import Mathlib.Tactic

/-!
# Preserve three original carriers through the Q/T/T/T canonicalization

The earlier source-preserving theorem remembers only the two translated owners
x,y.  Since they are distinct members of a three-element original carrier set
{u,v,w}, there is a third original carrier r distinct from both.

Feeding r's original enlarged-block membership into the strengthened Q/T/T/T
upgrade proves that the final saturated state contains all three original
sources: x,y and either the completion owner s or the third translated owner z.

This is the provenance form needed by minimal-core arguments.
-/

namespace JSP000404Research
namespace OrderedEdgeColoring

theorem exists_third_of_two_distinct_members_three
    {V : Type*} [DecidableEq V]
    {u v w x y : V}
    (huv : u ≠ v)
    (huw : u ≠ w)
    (hvw : v ≠ w)
    (hxy : x ≠ y)
    (hx : x ∈ ({u,v,w} : Finset V))
    (hy : y ∈ ({u,v,w} : Finset V)) :
    ∃ r : V,
      r ∈ ({u,v,w} : Finset V) ∧
      r ≠ x ∧ r ≠ y := by
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy ⊢
  rcases hx with rfl | rfl | rfl <;>
    rcases hy with rfl | rfl | rfl
  · exact False.elim (hxy rfl)
  · exact ⟨w,Or.inr (Or.inr rfl),huw.symm,hvw.symm⟩
  · exact ⟨v,Or.inr (Or.inl rfl),huv.symm,hvw⟩
  · exact ⟨w,Or.inr (Or.inr rfl),huw.symm,hvw.symm⟩
  · exact False.elim (hxy rfl)
  · exact ⟨u,Or.inl rfl,huv,huw⟩
  · exact ⟨v,Or.inr (Or.inl rfl),huv.symm,hvw⟩
  · exact ⟨u,Or.inl rfl,huv,huw⟩
  · exact False.elim (hxy rfl)

theorem threeSecond_commonWord_QTTT_or_closed_with_three_sources
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexpLt : ∀ q, exponent q < n)
    (hexp : ∀ q, exponent q ≤ n)
    (honeLoss :
      ∀ q, (active C q).card ≤ n - exponent q + 1)
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
        (s ∈ ({u,v,w} : Finset V) ∨
          z ∈ ({u,v,w} : Finset V)) ∧
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

    obtain ⟨r,hrSource,hrx,hry⟩ :=
      exists_third_of_two_distinct_members_three
        huv huw hvw hxy hxSource hySource

    have loss_of_source :
        ∀ {q : V},
          q ∈ ({u,v,w} : Finset V) →
          q ∈ projectedLossVertices C exponent := by
      intro q hq
      simp only [Finset.mem_insert, Finset.mem_singleton] at hq
      rcases hq with rfl | rfl | rfl
      · exact huLoss
      · exact hvLoss
      · exact hwLoss

    have second_of_source :
        ∀ {q : V},
          q ∈ ({u,v,w} : Finset V) →
          exponent q = n - 2 := by
      intro q hq
      simp only [Finset.mem_insert, Finset.mem_singleton] at hq
      rcases hq with rfl | rfl | rfl
      · exact huSecond
      · exact hvSecond
      · exact hwSecond

    have block_of_source :
        ∀ {q : V},
          q ∈ ({u,v,w} : Finset V) →
          word ∈ enlargedProjectedCandidateBlock C exponent q := by
      intro q hq
      simp only [Finset.mem_insert, Finset.mem_singleton] at hq
      rcases hq with rfl | rfl | rfl
      · exact huBlock
      · exact hvBlock
      · exact hwBlock

    rcases
      QTT_hard_branch_upgrades_to_QTTT_preserving_third_source
        C exponent hexpLt hexp honeLoss
        hsx hsy hxy
        hrx.symm hry.symm
        hsLoss hxLoss hyLoss (loss_of_source hrSource)
        hsSecond hxSecond hySecond (second_of_source hrSource)
        hcx hcy hcxy hsQ hxT hyT
        (block_of_source hrSource)
      with hhole2 | hpaid2 | hexact2 | htop2 | hdeep2 | hQTTT
    · exact Or.inl hhole2
    · exact Or.inr (Or.inl hpaid2)
    · exact Or.inr (Or.inr (Or.inl hexact2))
    · exact Or.inr (Or.inr (Or.inr (Or.inl htop2)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hdeep2))))
    · obtain ⟨z,cz,hsz,hxz,hyz,
        hzLoss,hzSecond,
        _hcxS,_hcyS,_hczS,
        hcxy',hcxz,hcyz,hsActive,
        hcxX,hcyY,hczZ,
        hsQ',hxT',hyT',hzT,
        hsourceThird⟩ := hQTTT
      have hthirdMem :
          s ∈ ({u,v,w} : Finset V) ∨
          z ∈ ({u,v,w} : Finset V) := by
        rcases hsourceThird with hsr | hzr
        · left
          rw [hsr]
          exact hrSource
        · right
          rw [hzr]
          exact hrSource
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        ⟨s,x,y,z,cx,cy,cz,
          hsx,hsy,hsz,hxy,hxz,hyz,
          hxSource,hySource,hthirdMem,
          hsLoss,hxLoss,hyLoss,hzLoss,
          hsSecond,hxSecond,hySecond,hzSecond,
          hcxX,hcyY,hczZ,
          hcxy',hcxz,hcyz,hsActive,
          hsQ',hxT',hyT',hzT⟩))))

#print axioms exists_third_of_two_distinct_members_three
#print axioms threeSecond_commonWord_QTTT_or_closed_with_three_sources

end OrderedEdgeColoring
end JSP000404Research
