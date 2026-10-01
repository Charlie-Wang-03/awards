import JSP000404Research.ResidualTripleFibreOutlet
import JSP000404Research.ResidualLossThreeExitRecursiveOutlet
import Mathlib.Tactic

/-!
# Canonical second-layer triple obstruction

A translated word at a second-layer projected-loss vertex comes from flipping
one of exactly three active coordinates of an original completion word.

Apply the three-exit theorem to that original word.  The translated word itself
is one of those three exits.  Therefore, unless a hole or positive-surplus
outlet already appears, the translated word has a completion blocker.  The
blocker profile is exact or loss; after exponent classification the only hard
case is another second-layer loss blocker.

Combining this with the fact that a triple loss word is translated at at least
two distinct loss vertices yields the canonical hard state

    word ∈ Q_s ∩ T_{u,c} ∩ T_{v,d}

for three distinct second-layer loss vertices s,u,v and distinct owner
coordinates c,d.
-/

namespace JSP000404Research
namespace OrderedEdgeColoring

theorem secondLayer_translated_word_blocker_or_closed
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexpLt : ∀ z, exponent z < n)
    (hexp : ∀ z, exponent z ≤ n)
    (honeLoss :
      ∀ z, (active C z).card ≤ n - exponent z + 1)
    {v : V}
    (hvLoss : v ∈ projectedLossVertices C exponent)
    (hvSecond : exponent v = n - 2)
    {word : Fin n → Bool}
    {c : Fin n}
    (hc : c ∈ retainedActive C v)
    (hwordT : word ∈ translatedCompletionWords C v c) :
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
      ∃ z : V,
        z ≠ v ∧
        z ∈ projectedLossVertices C exponent ∧
        exponent z = n - 2 ∧
        word ∈ retainedCompletionWords C z
    ) := by
  classical
  let base := flipBoolWordAt word c
  have hbase :
      base ∈ retainedCompletionWords C v := by
    exact (mem_translatedCompletionWords C v c word).1 hwordT

  rcases
    secondLayerLoss_three_exit_hole_or_paid_or_disjoint_exact_loss_fibres
      C exponent hexp honeLoss
      hvLoss hvSecond hbase
    with hhole | hpaid | hhard
  · obtain ⟨e,he,hole⟩ := hhole
    exact Or.inl ⟨flipBoolWordAt base e,hole⟩
  · exact Or.inr (Or.inl hpaid)
  · obtain ⟨a,b,d,ha,hb,hd,hab,had,hbd,
      haNonempty,hbNonempty,hdNonempty,
      _haCard,_hbCard,_hdCard,
      _habDisj,_hadDisj,_hbdDisj,hprofile⟩ := hhard

    have hcCase : c = a ∨ c = b ∨ c = d := by
      by_contra hnot
      push_neg at hnot
      have hsub :
          ({a,b,d,c} : Finset (Fin n)) ⊆ retainedActive C v := by
        intro e he
        simp only [Finset.mem_insert, Finset.mem_singleton] at he
        rcases he with rfl | rfl | rfl | rfl
        · exact ha
        · exact hb
        · exact hd
        · exact hc
      have hcard4 :
          ({a,b,d,c} : Finset (Fin n)).card = 4 := by
        simp [hab,had,hbd,hnot.1,hnot.2.1,hnot.2.2]
      have hfour :
          4 ≤ (retainedActive C v).card := by
        rw [← hcard4]
        exact Finset.card_le_card hsub
      have hthree :=
        secondLayerLoss_retainedActive_card_eq_three
          C exponent hvLoss hvSecond
      omega

    have hwordFibre :
        (completionFibre C word).Nonempty := by
      rcases hcCase with hca | hcb | hcd
      · have h := haNonempty
        subst a
        simpa [base, flipBoolWordAt_involutive] using h
      · have h := hbNonempty
        subst b
        simpa [base, flipBoolWordAt_involutive] using h
      · have h := hdNonempty
        subst d
        simpa [base, flipBoolWordAt_involutive] using h

    obtain ⟨z,hzF⟩ := hwordFibre
    have hzWord :
        word ∈ retainedCompletionWords C z :=
      (mem_completionFibre C word z).1 hzF

    have hzHard :
        z ≠ v ∧
        (ExactProjectedBudget C exponent z
          ∨ z ∈ projectedLossVertices C exponent) := by
      rcases hcCase with hca | hcb | hcd
      · apply hprofile z
        left
        simpa [base,hca,flipBoolWordAt_involutive] using hzF
      · apply hprofile z
        right; left
        simpa [base,hcb,flipBoolWordAt_involutive] using hzF
      · apply hprofile z
        right; right
        simpa [base,hcd,flipBoolWordAt_involutive] using hzF

    rcases hzHard.2 with hzExact | hzLoss
    · exact Or.inr (Or.inr (Or.inl ⟨z,hzExact⟩))
    · rcases exponent_top_second_or_deep
        exponent (hexpLt z)
      with hzTop | hzSecond | hzDeep
      · exact Or.inr (Or.inr (Or.inr
          (Or.inl ⟨z,hzLoss,hzTop⟩)))
      · exact Or.inr (Or.inr (Or.inr
          (Or.inr (Or.inr
            ⟨z,hzHard.1,hzLoss,hzSecond,hzWord⟩))))
      · exact Or.inr (Or.inr (Or.inr
          (Or.inr (Or.inl ⟨z,hzLoss,hzDeep⟩))))

/-- Canonicalization of a common word carried by three second-layer loss
blocks.  Unless a standard closed outlet appears, one obtains a unique-form
Q/T/T witness on three distinct second-layer loss vertices. -/
theorem threeSecond_commonWord_QTT_or_closed
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
          hsLoss,hvLoss,hwLoss,
          hsSecond,hvSecond,hwSecond,
          hcv,hcw,hcvw,hsQ,hvT,hwT⟩))))

#print axioms secondLayer_translated_word_blocker_or_closed
#print axioms threeSecond_commonWord_QTT_or_closed

end OrderedEdgeColoring
end JSP000404Research
