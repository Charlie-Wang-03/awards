import JSP000404Research.ResidualQTTThirdSourceProvenance
import JSP000404Research.ResidualSecondLayerTripleCanonical
import Mathlib.Tactic

/-!
# Q/T/T -> Q/T/T/T while preserving the third original source

Given a hard Q/T/T state whose two translated owners x,y came from a
three-source common-word obstruction, retain the third source r explicitly.

The previous provenance lemma says either r=s, or r is already translated at
a third coordinate cz distinct from cx,cy.

* If r=s, use the existing unique-third-exit upgrade.  The resulting Q/T/T/T
  state records that the completion owner is the third source.
* If r is translated, no fresh blocker is needed: set z=r.  Q/T owner-edge
  semantics makes cz active at s; together with cx,cy and card=3 this gives
  the exact completion-owner palette {cx,cy,cz}.

Hence every hard Q/T/T/T state can preserve three original source vertices:
x,y and either s or z.
-/

namespace JSP000404Research
namespace OrderedEdgeColoring

theorem QTT_hard_branch_upgrades_to_QTTT_preserving_third_source
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexpLt : ∀ q, exponent q < n)
    (hexp : ∀ q, exponent q ≤ n)
    (honeLoss :
      ∀ q, (active C q).card ≤ n - exponent q + 1)
    {s x y r : V}
    (hsx : s ≠ x)
    (hsy : s ≠ y)
    (hxy : x ≠ y)
    (hxr : x ≠ r)
    (hyr : y ≠ r)
    (hsLoss : s ∈ projectedLossVertices C exponent)
    (hxLoss : x ∈ projectedLossVertices C exponent)
    (hyLoss : y ∈ projectedLossVertices C exponent)
    (hrLoss : r ∈ projectedLossVertices C exponent)
    (hsSecond : exponent s = n - 2)
    (hxSecond : exponent x = n - 2)
    (hySecond : exponent y = n - 2)
    (hrSecond : exponent r = n - 2)
    {word : Fin n → Bool}
    {cx cy : Fin n}
    (hcx : cx ∈ retainedActive C x)
    (hcy : cy ∈ retainedActive C y)
    (hcxy : cx ≠ cy)
    (hsQ : word ∈ retainedCompletionWords C s)
    (hxT : word ∈ translatedCompletionWords C x cx)
    (hyT : word ∈ translatedCompletionWords C y cy)
    (hrBlock :
      word ∈ enlargedProjectedCandidateBlock C exponent r) :
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
      ∃ z : V,
      ∃ cz : Fin n,
        s ≠ z ∧ x ≠ z ∧ y ≠ z ∧
        z ∈ projectedLossVertices C exponent ∧
        exponent z = n - 2 ∧
        cx ∈ retainedActive C s ∧
        cy ∈ retainedActive C s ∧
        cz ∈ retainedActive C s ∧
        cx ≠ cy ∧ cx ≠ cz ∧ cy ≠ cz ∧
        retainedActive C s = {cx,cy,cz} ∧
        cx ∈ retainedActive C x ∧
        cy ∈ retainedActive C y ∧
        cz ∈ retainedActive C z ∧
        word ∈ retainedCompletionWords C s ∧
        word ∈ translatedCompletionWords C x cx ∧
        word ∈ translatedCompletionWords C y cy ∧
        word ∈ translatedCompletionWords C z cz ∧
        (s = r ∨ z = r)
    ) := by
  have hthird :=
    QTT_third_source_is_Q_owner_or_third_translated
      C exponent hexp honeLoss
      hsx hsy hxr hyr
      hsLoss hxLoss hyLoss hrLoss
      hcxy hsQ hxT hyT hrBlock
  rcases hthird with hrs | hthirdT
  · subst r
    rcases
      QTT_hard_branch_upgrades_to_QTTT
        C exponent hexpLt hexp honeLoss
        hsx hsy hxy
        hsLoss hxLoss hyLoss
        hsSecond hxSecond hySecond
        hcx hcy hcxy hsQ hxT hyT
      with hhole | hpaid | hexact | htop | hdeep | hQTTT
    · exact Or.inl hhole
    · exact Or.inr (Or.inl hpaid)
    · exact Or.inr (Or.inr (Or.inl hexact))
    · exact Or.inr (Or.inr (Or.inr (Or.inl htop)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hdeep))))
    · obtain ⟨cz,z,hsz,hxz,hyz,
        hzLoss,hzSecond,
        hcxS,hcyS,hczS,
        hcxy',hcxz,hcyz,hsActive,
        hcxX,hcyY,hczZ,
        hsQ',hxT',hyT',hzT⟩ := hQTTT
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        ⟨z,cz,hsz,hxz,hyz,
          hzLoss,hzSecond,
          hcxS,hcyS,hczS,
          hcxy',hcxz,hcyz,hsActive,
          hcxX,hcyY,hczZ,
          hsQ',hxT',hyT',hzT,
          Or.inl rfl⟩))))
  · obtain ⟨cz,hczR,hcxz,hcyz,hrT⟩ := hthirdT
    have hrs : s ≠ r := by
      intro h
      subst r
      exact Finset.disjoint_left.mp
        (translatedCompletionWords_disjoint_original_of_active
          C hczR) hrT hsQ
    have hczS : cz ∈ retainedActive C s := by
      have hsem :=
        QTT_owner_edge_semantics
          C exponent hexp honeLoss
          hrs hrLoss hczR hsQ hrT
      rcases hsem with hleft | hright
      · obtain ⟨hrslt,hret,hcol,_⟩ := hleft
        have hm :=
          retainedColor_mem_retainedActive_right
            C hrslt hret
        simpa [hcol] using hm
      · obtain ⟨hsrlt,hret,hcol,_⟩ := hright
        have hm :=
          retainedColor_mem_retainedActive_left
            C hsrlt hret
        simpa [hcol] using hm

    have hknown :=
      QTT_two_known_active_coordinates_at_completion_owner
        C exponent hexp honeLoss
        hsx hsy hxLoss hyLoss
        hcx hcy hsQ hxT hyT
    have hsCard :=
      secondLayerLoss_retainedActive_card_eq_three
        C exponent hsLoss hsSecond
    have hsub :
        ({cx,cy,cz} : Finset (Fin n)) ⊆ retainedActive C s := by
      intro q hq
      simp only [Finset.mem_insert, Finset.mem_singleton] at hq
      rcases hq with rfl | rfl | rfl
      · exact hknown.1
      · exact hknown.2
      · exact hczS
    have hsetCard :
        ({cx,cy,cz} : Finset (Fin n)).card = 3 := by
      simp [hcxy,hcxz,hcyz]
    have hsActive :
        retainedActive C s = {cx,cy,cz} := by
      apply Finset.eq_of_subset_of_card_le
      · exact hsub
      · simpa [hsCard,hsetCard]

    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      ⟨r,cz,hrs,hxr,hyr,
        hrLoss,hrSecond,
        hknown.1,hknown.2,hczS,
        hcxy,hcxz,hcyz,hsActive,
        hcx,hcy,hczR,
        hsQ,hxT,hyT,hrT,
        Or.inr rfl⟩))))

#print axioms QTT_hard_branch_upgrades_to_QTTT_preserving_third_source

end OrderedEdgeColoring
end JSP000404Research
