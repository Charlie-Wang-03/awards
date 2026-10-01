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


/-- In a canonical Q/T/T obstruction, each translated owner coordinate is
exactly the retained colour of the edge joining that translated owner to the
completion owner.  The side of the completion owner also determines the
translated word bit at that coordinate. -/
theorem QTT_owner_edge_semantics
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexp : ∀ z, exponent z ≤ n)
    (honeLoss :
      ∀ z, (active C z).card ≤ n - exponent z + 1)
    {s x : V}
    (hsx : s ≠ x)
    (hxLoss : x ∈ projectedLossVertices C exponent)
    {word : Fin n → Bool}
    {cx : Fin n}
    (hcx : cx ∈ retainedActive C x)
    (hsQ : word ∈ retainedCompletionWords C s)
    (hxT : word ∈ translatedCompletionWords C x cx) :
    (
      ∃ hxs : x < s,
        ∃ hret : (C.color x s).val < n,
          retainedColor C x s hret = cx ∧
          word cx = true
    )
    ∨
    (
      ∃ hsxlt : s < x,
        ∃ hret : (C.color s x).val < n,
          retainedColor C s x hret = cx ∧
          word cx = false
    ) := by
  have hxBase :
      flipBoolWordAt word cx ∈ retainedCompletionWords C x :=
    (mem_translatedCompletionWords C x cx word).1 hxT
  have hsAsFlip :
      flipBoolWordAt (flipBoolWordAt word cx) cx ∈
        retainedCompletionWords C s := by
    simpa [flipBoolWordAt_involutive] using hsQ
  have hedge :=
    loss_translated_blocker_edge_colour
      C exponent hexp honeLoss
      hxLoss hsx.symm hcx hxBase hsAsFlip
  rcases hedge with hright | hleft
  · obtain ⟨hxs,hret,hcol⟩ := hright
    left
    refine ⟨hxs,hret,hcol,?_⟩
    have hOut : cx ∈ outgoingRetained C x := by
      apply (mem_outgoingRetained_iff C x cx).2
      refine ⟨s,hxs,?_⟩
      apply Fin.ext
      have hval := congrArg Fin.val hcol
      simpa [retainedColor] using hval
    exact translated_loss_word_true_of_outgoing C hOut hxT
  · obtain ⟨hsxlt,hret,hcol⟩ := hleft
    right
    refine ⟨hsxlt,hret,hcol,?_⟩
    have hIn : cx ∈ incomingRetained C x := by
      apply (mem_incomingRetained_iff C x cx).2
      refine ⟨s,hsxlt,?_⟩
      apply Fin.ext
      have hval := congrArg Fin.val hcol
      simpa [retainedColor] using hval
    exact translated_loss_word_false_of_incoming C hIn hxT

/-- Both Q/T edges of a canonical Q/T/T obstruction use the corresponding
translated owner coordinates.  Consequently those two distinct coordinates
are active at the completion owner as well. -/
theorem QTT_two_known_active_coordinates_at_completion_owner
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexp : ∀ z, exponent z ≤ n)
    (honeLoss :
      ∀ z, (active C z).card ≤ n - exponent z + 1)
    {s x y : V}
    (hsx : s ≠ x)
    (hsy : s ≠ y)
    {word : Fin n → Bool}
    {cx cy : Fin n}
    (hxLoss : x ∈ projectedLossVertices C exponent)
    (hyLoss : y ∈ projectedLossVertices C exponent)
    (hcx : cx ∈ retainedActive C x)
    (hcy : cy ∈ retainedActive C y)
    (hsQ : word ∈ retainedCompletionWords C s)
    (hxT : word ∈ translatedCompletionWords C x cx)
    (hyT : word ∈ translatedCompletionWords C y cy) :
    cx ∈ retainedActive C s ∧
    cy ∈ retainedActive C s := by
  have hxSem :=
    QTT_owner_edge_semantics
      C exponent hexp honeLoss
      hsx hxLoss hcx hsQ hxT
  have hySem :=
    QTT_owner_edge_semantics
      C exponent hexp honeLoss
      hsy hyLoss hcy hsQ hyT
  constructor
  · rcases hxSem with hleft | hright
    · obtain ⟨hxs,hret,hcol,_⟩ := hleft
      have hc :
          retainedColor C x s hret ∈ retainedActive C s :=
        retainedColor_mem_retainedActive_right C hxs hret
      simpa [hcol] using hc
    · obtain ⟨hsxlt,hret,hcol,_⟩ := hright
      have hc :
          retainedColor C s x hret ∈ retainedActive C s :=
        retainedColor_mem_retainedActive_left C hsxlt hret
      simpa [hcol] using hc
  · rcases hySem with hleft | hright
    · obtain ⟨hys,hret,hcol,_⟩ := hleft
      have hc :
          retainedColor C y s hret ∈ retainedActive C s :=
        retainedColor_mem_retainedActive_right C hys hret
      simpa [hcol] using hc
    · obtain ⟨hsylt,hret,hcol,_⟩ := hright
      have hc :
          retainedColor C s y hret ∈ retainedActive C s :=
        retainedColor_mem_retainedActive_left C hsylt hret
      simpa [hcol] using hc

/-- At a second-layer completion owner in Q/T/T, the two translated-owner
coordinates occupy two of the three active slots, leaving a unique third active
coordinate. -/
theorem QTT_secondLayer_completion_owner_has_unique_third_active
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexp : ∀ z, exponent z ≤ n)
    (honeLoss :
      ∀ z, (active C z).card ≤ n - exponent z + 1)
    {s x y : V}
    (hsx : s ≠ x)
    (hsy : s ≠ y)
    (hsLoss : s ∈ projectedLossVertices C exponent)
    (hsSecond : exponent s = n - 2)
    {word : Fin n → Bool}
    {cx cy : Fin n}
    (hxLoss : x ∈ projectedLossVertices C exponent)
    (hyLoss : y ∈ projectedLossVertices C exponent)
    (hcx : cx ∈ retainedActive C x)
    (hcy : cy ∈ retainedActive C y)
    (hcxy : cx ≠ cy)
    (hsQ : word ∈ retainedCompletionWords C s)
    (hxT : word ∈ translatedCompletionWords C x cx)
    (hyT : word ∈ translatedCompletionWords C y cy) :
    ∃! e : Fin n,
      e ∈ retainedActive C s ∧ e ≠ cx ∧ e ≠ cy := by
  classical
  have hknown :=
    QTT_two_known_active_coordinates_at_completion_owner
      C exponent hexp honeLoss
      hsx hsy hxLoss hyLoss hcx hcy hsQ hxT hyT
  have hcard :=
    secondLayerLoss_retainedActive_card_eq_three
      C exponent hsLoss hsSecond
  have hexists :
      ∃ e ∈ retainedActive C s, e ≠ cx ∧ e ≠ cy := by
    by_contra hnone
    push_neg at hnone
    have hsub :
        retainedActive C s ⊆ {cx,cy} := by
      intro e he
      have heq := hnone e he
      simp [heq]
    have hle := Finset.card_le_card hsub
    simp [hcard,hcxy] at hle
  obtain ⟨e,he,hecx,hecy⟩ := hexists
  refine ⟨e,⟨he,hecx,hecy⟩,?_⟩
  intro d hd
  by_contra hde
  have hsub :
      ({cx,cy,e,d} : Finset (Fin n)) ⊆ retainedActive C s := by
    intro q hq
    simp only [Finset.mem_insert, Finset.mem_singleton] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact hknown.1
    · exact hknown.2
    · exact he
    · exact hd.1
  have hcard4 :
      ({cx,cy,e,d} : Finset (Fin n)).card = 4 := by
    simp [hcxy,hecx,hecy,hd.2.1,hd.2.2,hde]
  have hfour : 4 ≤ (retainedActive C s).card := by
    rw [← hcard4]
    exact Finset.card_le_card hsub
  omega

#print axioms QTT_owner_edge_semantics
#print axioms QTT_two_known_active_coordinates_at_completion_owner
#print axioms QTT_secondLayer_completion_owner_has_unique_third_active


/-- A canonical second-layer Q/T/T configuration either closes immediately
through the unique third active exit of the completion owner, or produces a
fresh fourth blocker vertex.  Freshness from both translated owners follows
from pairwise disjointness of the three single-flip blocker fibres. -/
theorem QTT_unique_third_exit_fresh_blocker_or_closed
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexpLt : ∀ z, exponent z < n)
    (hexp : ∀ z, exponent z ≤ n)
    (honeLoss :
      ∀ z, (active C z).card ≤ n - exponent z + 1)
    {s x y : V}
    (hsx : s ≠ x)
    (hsy : s ≠ y)
    (hxy : x ≠ y)
    (hsLoss : s ∈ projectedLossVertices C exponent)
    (hxLoss : x ∈ projectedLossVertices C exponent)
    (hyLoss : y ∈ projectedLossVertices C exponent)
    (hsSecond : exponent s = n - 2)
    {word : Fin n → Bool}
    {cx cy : Fin n}
    (hcx : cx ∈ retainedActive C x)
    (hcy : cy ∈ retainedActive C y)
    (hcxy : cx ≠ cy)
    (hsQ : word ∈ retainedCompletionWords C s)
    (hxT : word ∈ translatedCompletionWords C x cx)
    (hyT : word ∈ translatedCompletionWords C y cy) :
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
      ∃ e : Fin n,
      ∃ z : V,
        e ∈ retainedActive C s ∧
        e ≠ cx ∧
        e ≠ cy ∧
        z ≠ s ∧ z ≠ x ∧ z ≠ y ∧
        z ∈ projectedLossVertices C exponent ∧
        exponent z = n - 2 ∧
        flipBoolWordAt word e ∈ retainedCompletionWords C z
    ) := by
  classical
  obtain ⟨e,he,heUnique⟩ :=
    QTT_secondLayer_completion_owner_has_unique_third_active
      C exponent hexp honeLoss
      hsx hsy hsLoss hsSecond
      hxLoss hyLoss hcx hcy hcxy
      hsQ hxT hyT

  have hsSingle :=
    projectedLoss_word_is_singleCompletionWord
      C exponent hexp honeLoss hsLoss hsQ

  have hxBlock :
      flipBoolWordAt word cx ∈ retainedCompletionWords C x :=
    (mem_translatedCompletionWords C x cx word).1 hxT
  have hyBlock :
      flipBoolWordAt word cy ∈ retainedCompletionWords C y :=
    (mem_translatedCompletionWords C y cy word).1 hyT

  by_cases heHole :
      flipBoolWordAt word e ∉ coveredCompletionWords C
  · exact Or.inl ⟨flipBoolWordAt word e,heHole⟩
  · have heCovered :
        flipBoolWordAt word e ∈ coveredCompletionWords C := by
      simpa using heHole
    have heNonempty :=
      (mem_coveredCompletionWords C
        (flipBoolWordAt word e)).1 heCovered
    obtain ⟨z,hzF⟩ := heNonempty
    have hzBlock :
        flipBoolWordAt word e ∈ retainedCompletionWords C z :=
      (mem_completionFibre C
        (flipBoolWordAt word e) z).1 hzF

    have heNeCx : e ≠ cx := he.2.1
    have heNeCy : e ≠ cy := he.2.2

    have hzNeS :
        z ≠ s :=
      single_flip_blocker_ne_owner
        C hsSingle he.1 hzBlock

    have hxeDisj :=
      two_single_flips_have_disjoint_blocker_fibres
        C hsSingle he.1
        (QTT_two_known_active_coordinates_at_completion_owner
          C exponent hexp honeLoss hsx hsy
          hxLoss hyLoss hcx hcy hsQ hxT hyT).1
        heNeCx
    have hyeDisj :=
      two_single_flips_have_disjoint_blocker_fibres
        C hsSingle he.1
        (QTT_two_known_active_coordinates_at_completion_owner
          C exponent hexp honeLoss hsx hsy
          hxLoss hyLoss hcx hcy hsQ hxT hyT).2
        heNeCy

    have hxF :
        x ∈ completionFibre C (flipBoolWordAt word cx) :=
      (mem_completionFibre C
        (flipBoolWordAt word cx) x).2 hxBlock
    have hyF :
        y ∈ completionFibre C (flipBoolWordAt word cy) :=
      (mem_completionFibre C
        (flipBoolWordAt word cy) y).2 hyBlock

    have hzNeX : z ≠ x := by
      intro hzx
      subst z
      exact Finset.disjoint_left.mp hxeDisj hzF hxF
    have hzNeY : z ≠ y := by
      intro hzy
      subst z
      exact Finset.disjoint_left.mp hyeDisj hzF hyF

    rcases projectedProfile_strict_exact_or_loss
        C exponent hexp honeLoss z
      with hzStrict | hzExact | hzLoss
    · exact Or.inr (Or.inl
        ⟨z,
          projected_strict_surplus_at_least_one
            exponent (projectedFree C) hzStrict⟩)
    · exact Or.inr (Or.inr (Or.inl ⟨z,hzExact⟩))
    · rcases exponent_top_second_or_deep
        exponent (hexpLt z)
      with hzTop | hzSecond | hzDeep
      · exact Or.inr (Or.inr (Or.inr
          (Or.inl ⟨z,hzLoss,hzTop⟩)))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
          ⟨e,z,he.1,he.2.1,he.2.2,
            hzNeS,hzNeX,hzNeY,hzLoss,hzSecond,hzBlock⟩))))
      · exact Or.inr (Or.inr (Or.inr
          (Or.inr (Or.inl ⟨z,hzLoss,hzDeep⟩))))

#print axioms QTT_unique_third_exit_fresh_blocker_or_closed


/-- In the hard third-exit branch, the fresh loss blocker must itself activate
the third coordinate.  Otherwise its completion cube is invariant under that
flip, so the original QTT word would lie simultaneously in the two distinct
loss completion cubes Q_s and Q_z. -/
theorem QTT_fresh_loss_blocker_third_coordinate_active
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexp : ∀ q, exponent q ≤ n)
    (honeLoss :
      ∀ q, (active C q).card ≤ n - exponent q + 1)
    {s z : V}
    (hsz : s ≠ z)
    (hsLoss : s ∈ projectedLossVertices C exponent)
    (hzLoss : z ∈ projectedLossVertices C exponent)
    {word : Fin n → Bool}
    {e : Fin n}
    (hsQ : word ∈ retainedCompletionWords C s)
    (hzFlip :
      flipBoolWordAt word e ∈ retainedCompletionWords C z) :
    e ∈ retainedActive C z := by
  by_contra heInactive
  have hzQ :
      word ∈ retainedCompletionWords C z :=
    (mem_completion_iff_flip_of_inactive C heInactive).1 hzFlip
  exact Finset.disjoint_left.mp
    (projectedLoss_completion_disjoint
      C exponent hexp honeLoss hsLoss hsz)
    hsQ hzQ

/-- Hence the fresh third-exit blocker is genuinely a translated carrier of
the original QTT word. -/
theorem QTT_fresh_loss_blocker_gives_translated_carrier
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexp : ∀ q, exponent q ≤ n)
    (honeLoss :
      ∀ q, (active C q).card ≤ n - exponent q + 1)
    {s z : V}
    (hsz : s ≠ z)
    (hsLoss : s ∈ projectedLossVertices C exponent)
    (hzLoss : z ∈ projectedLossVertices C exponent)
    {word : Fin n → Bool}
    {e : Fin n}
    (hsQ : word ∈ retainedCompletionWords C s)
    (hzFlip :
      flipBoolWordAt word e ∈ retainedCompletionWords C z) :
    e ∈ retainedActive C z ∧
      word ∈ translatedCompletionWords C z e := by
  have heActive :=
    QTT_fresh_loss_blocker_third_coordinate_active
      C exponent hexp honeLoss
      hsz hsLoss hzLoss hsQ hzFlip
  exact ⟨heActive,
    (mem_translatedCompletionWords C z e word).2 hzFlip⟩

#print axioms QTT_fresh_loss_blocker_third_coordinate_active
#print axioms QTT_fresh_loss_blocker_gives_translated_carrier


/-- The translated--translated edge in a canonical Q/T/T obstruction uses one
of the two translated owner coordinates. -/
theorem QTT_translated_edge_colour_one_of_owners
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexp : ∀ z, exponent z ≤ n)
    (honeLoss :
      ∀ z, (active C z).card ≤ n - exponent z + 1)
    {x y : V}
    (hxy : x ≠ y)
    (hxLoss : x ∈ projectedLossVertices C exponent)
    (hyLoss : y ∈ projectedLossVertices C exponent)
    {word : Fin n → Bool}
    {cx cy : Fin n}
    (hcx : cx ∈ retainedActive C x)
    (hcy : cy ∈ retainedActive C y)
    (hxT : word ∈ translatedCompletionWords C x cx)
    (hyT : word ∈ translatedCompletionWords C y cy) :
    (
      ∃ hlt : x < y,
        ∃ hret : (C.color x y).val < n,
          retainedColor C x y hret = cx ∨
          retainedColor C x y hret = cy
    )
    ∨
    (
      ∃ hlt : y < x,
        ∃ hret : (C.color y x).val < n,
          retainedColor C y x hret = cx ∨
          retainedColor C y x hret = cy
    ) := by
  exact translated_loss_conflict_edge_colour
    C exponent hexp honeLoss
    hxLoss hyLoss hxy hxT hyT

/-- Order-sensitive two-colour triangle law for Q/T/T.

The two completion-owner edges have colours cx and cy.  If one translated
owner lies between the completion owner and the other translated owner, the
no-monochromatic-two-path axiom forces the translated--translated edge to use
the opposite colour.

The only unconstrained ordering is when the completion owner itself is the
middle vertex: its two incident colours are already distinct, so the outer
edge may use either cx or cy. -/
theorem QTT_ordered_two_colour_triangle
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexp : ∀ z, exponent z ≤ n)
    (honeLoss :
      ∀ z, (active C z).card ≤ n - exponent z + 1)
    {s x y : V}
    (hsx : s ≠ x)
    (hsy : s ≠ y)
    (hxy : x ≠ y)
    (hxLoss : x ∈ projectedLossVertices C exponent)
    (hyLoss : y ∈ projectedLossVertices C exponent)
    {word : Fin n → Bool}
    {cx cy : Fin n}
    (hcx : cx ∈ retainedActive C x)
    (hcy : cy ∈ retainedActive C y)
    (hcxy : cx ≠ cy)
    (hsQ : word ∈ retainedCompletionWords C s)
    (hxT : word ∈ translatedCompletionWords C x cx)
    (hyT : word ∈ translatedCompletionWords C y cy) :
    (
      x < s ∧ s < y ∧
      word cx = true ∧ word cy = false
    )
    ∨
    (
      y < s ∧ s < x ∧
      word cy = true ∧ word cx = false
    )
    ∨
    (
      s < x ∧ x < y ∧
      ∃ hret : (C.color x y).val < n,
        retainedColor C x y hret = cy
    )
    ∨
    (
      s < y ∧ y < x ∧
      ∃ hret : (C.color y x).val < n,
        retainedColor C y x hret = cx
    )
    ∨
    (
      x < y ∧ y < s ∧
      ∃ hret : (C.color x y).val < n,
        retainedColor C x y hret = cx
    )
    ∨
    (
      y < x ∧ x < s ∧
      ∃ hret : (C.color y x).val < n,
        retainedColor C y x hret = cy
    ) := by
  have hxSem :=
    QTT_owner_edge_semantics
      C exponent hexp honeLoss
      hsx hxLoss hcx hsQ hxT
  have hySem :=
    QTT_owner_edge_semantics
      C exponent hexp honeLoss
      hsy hyLoss hcy hsQ hyT
  have hxySem :=
    QTT_translated_edge_colour_one_of_owners
      C exponent hexp honeLoss
      hxy hxLoss hyLoss hcx hcy hxT hyT
  rcases hxSem with hxLeft | hxRight <;>
    rcases hySem with hyLeft | hyRight
  · obtain ⟨hxs,hxret,hxcol,hxTrue⟩ := hxLeft
    obtain ⟨hys,hyret,hycol,hyTrue⟩ := hyLeft
    rcases lt_or_gt_of_ne hxy with hxylt | hyxlt
    · right; right; right; right
      left
      refine ⟨hxylt,hys,?_⟩
      · rcases hxySem with hforward | hbackward
        · obtain ⟨_,hret,hcol⟩ := hforward
          rcases hcol with hcxCol | hcyCol
          · exact ⟨hret,hcxCol⟩
          · have hmono :
                C.color x y ≠ C.color y s :=
              C.noMonoTwoPath hxylt hys
            exfalso
            apply hmono
            apply Fin.ext
            have h1 := congrArg Fin.val hcyCol
            have h2 := congrArg Fin.val hycol
            simpa [retainedColor] using h1.trans h2.symm
        · exact False.elim ((not_lt_of_ge hxylt.le) hbackward.1)
    · right; right; right; right; right
      refine ⟨hyxlt,hxs,?_⟩
      · rcases hxySem with hforward | hbackward
        · exact False.elim ((not_lt_of_ge hyxlt.le) hforward.1)
        · obtain ⟨_,hret,hcol⟩ := hbackward
          rcases hcol with hcxCol | hcyCol
          · have hmono :
                C.color y x ≠ C.color x s :=
              C.noMonoTwoPath hyxlt hxs
            exfalso
            apply hmono
            apply Fin.ext
            have h1 := congrArg Fin.val hcxCol
            have h2 := congrArg Fin.val hxcol
            simpa [retainedColor] using h1.trans h2.symm
          · exact ⟨hret,hcyCol⟩
  · obtain ⟨hxs,_hxret,_hxcol,hxTrue⟩ := hxLeft
    obtain ⟨hsy,_hyret,_hycol,hyFalse⟩ := hyRight
    exact Or.inl ⟨hxs,hsy,hxTrue,hyFalse⟩
  · obtain ⟨hsxlt,_hxret,_hxcol,hxFalse⟩ := hxRight
    obtain ⟨hys,_hyret,_hycol,hyTrue⟩ := hyLeft
    exact Or.inr (Or.inl ⟨hys,hsxlt,hyTrue,hxFalse⟩)
  · obtain ⟨hsxlt,hxret,hxcol,_hxFalse⟩ := hxRight
    obtain ⟨hsylt,hyret,hycol,_hyFalse⟩ := hyRight
    rcases lt_or_gt_of_ne hxy with hxylt | hyxlt
    · right; right
      left
      refine ⟨hsxlt,hxylt,?_⟩
      rcases hxySem with hforward | hbackward
      · obtain ⟨_,hret,hcol⟩ := hforward
        rcases hcol with hcxCol | hcyCol
        · have hmono :
              C.color s x ≠ C.color x y :=
            C.noMonoTwoPath hsxlt hxylt
          exfalso
          apply hmono
          apply Fin.ext
          have h1 := congrArg Fin.val hxcol
          have h2 := congrArg Fin.val hcxCol
          simpa [retainedColor] using h1.trans h2.symm
        · exact ⟨hret,hcyCol⟩
      · exact False.elim ((not_lt_of_ge hxylt.le) hbackward.1)
    · right; right; right
      left
      refine ⟨hsylt,hyxlt,?_⟩
      rcases hxySem with hforward | hbackward
      · exact False.elim ((not_lt_of_ge hyxlt.le) hforward.1)
      · obtain ⟨_,hret,hcol⟩ := hbackward
        rcases hcol with hcxCol | hcyCol
        · exact ⟨hret,hcxCol⟩
        · have hmono :
              C.color s y ≠ C.color y x :=
            C.noMonoTwoPath hsylt hyxlt
          exfalso
          apply hmono
          apply Fin.ext
          have h1 := congrArg Fin.val hycol
          have h2 := congrArg Fin.val hcyCol
          simpa [retainedColor] using h1.trans h2.symm

#print axioms QTT_translated_edge_colour_one_of_owners
#print axioms QTT_ordered_two_colour_triangle

end OrderedEdgeColoring
end JSP000404Research
