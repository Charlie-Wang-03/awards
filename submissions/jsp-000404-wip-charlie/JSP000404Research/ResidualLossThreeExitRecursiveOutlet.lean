import JSP000404Research.ResidualLossTwoExitRecursiveOutlet
import JSP000404Research.ResidualEnlargedCollisionSimpleGraph
import Mathlib.Tactic

/-!
# Three-exit recursive outlet for second-layer projected-loss words

A projected-loss vertex with exponent n-2 has exactly three retained-active
coordinates. For a completion word at such a vertex, the three one-bit flip
fibres are pairwise disjoint.

Thus either:
* one active flip is a Boolean hole;
* some blocker is strict and supplies one surplus token; or
* all three blocker fibres are nonempty, pairwise disjoint, cardinality <= 2,
  and every blocker is exact or projected-loss.

The final hard branch therefore yields three disjoint exact/loss descendant
fibres.
-/

namespace JSP000404Research
namespace OrderedEdgeColoring

theorem secondLayerLoss_retainedActive_card_eq_three
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    {v : V}
    (hvLoss : v ∈ projectedLossVertices C exponent)
    (hvSecond : exponent v = n - 2) :
    (retainedActive C v).card = 3 := by
  rw [projectedLoss_retainedActive_card
    C exponent hvLoss, hvSecond]
  have hn3 : 3 ≤ n := by
    have heq :=
      (mem_projectedLossVertices C exponent v).1 hvLoss
    unfold projectedFree at heq
    omega
  omega

theorem secondLayerLoss_exists_three_distinct_active
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    {v : V}
    (hvLoss : v ∈ projectedLossVertices C exponent)
    (hvSecond : exponent v = n - 2) :
    ∃ a b c : Fin n,
      a ∈ retainedActive C v ∧
      b ∈ retainedActive C v ∧
      c ∈ retainedActive C v ∧
      a ≠ b ∧ a ≠ c ∧ b ≠ c := by
  classical
  have hcard :=
    secondLayerLoss_retainedActive_card_eq_three
      C exponent hvLoss hvSecond
  obtain ⟨a,b,c,hab,hac,hbc,hEq⟩ :=
    Finset.card_eq_three.mp hcard
  refine ⟨a,b,c,?_,?_,?_,hab,hac,hbc⟩
  · rw [hEq]; simp
  · rw [hEq]; simp
  · rw [hEq]; simp

theorem secondLayerLoss_three_exit_hole_or_paid_or_disjoint_exact_loss_fibres
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexp : ∀ z, exponent z ≤ n)
    (honeLoss :
      ∀ z, (active C z).card ≤ n - exponent z + 1)
    {v : V}
    (hvLoss : v ∈ projectedLossVertices C exponent)
    (hvSecond : exponent v = n - 2)
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
      ∃ a b c : Fin n,
        a ∈ retainedActive C v ∧
        b ∈ retainedActive C v ∧
        c ∈ retainedActive C v ∧
        a ≠ b ∧ a ≠ c ∧ b ≠ c ∧
        (completionFibre C (flipBoolWordAt word a)).Nonempty ∧
        (completionFibre C (flipBoolWordAt word b)).Nonempty ∧
        (completionFibre C (flipBoolWordAt word c)).Nonempty ∧
        (completionFibre C (flipBoolWordAt word a)).card ≤ 2 ∧
        (completionFibre C (flipBoolWordAt word b)).card ≤ 2 ∧
        (completionFibre C (flipBoolWordAt word c)).card ≤ 2 ∧
        Disjoint
          (completionFibre C (flipBoolWordAt word a))
          (completionFibre C (flipBoolWordAt word b)) ∧
        Disjoint
          (completionFibre C (flipBoolWordAt word a))
          (completionFibre C (flipBoolWordAt word c)) ∧
        Disjoint
          (completionFibre C (flipBoolWordAt word b))
          (completionFibre C (flipBoolWordAt word c)) ∧
        ∀ w : V,
          (
            w ∈ completionFibre C (flipBoolWordAt word a)
            ∨
            w ∈ completionFibre C (flipBoolWordAt word b)
            ∨
            w ∈ completionFibre C (flipBoolWordAt word c)
          ) →
          w ≠ v ∧
          (
            ExactProjectedBudget C exponent w
            ∨
            w ∈ projectedLossVertices C exponent
          )
    ) := by
  classical
  obtain ⟨a,b,c,ha,hb,hc,hab,hac,hbc⟩ :=
    secondLayerLoss_exists_three_distinct_active
      C exponent hvLoss hvSecond

  have hsingle :=
    projectedLoss_word_is_singleCompletionWord
      C exponent hexp honeLoss hvLoss hword

  by_cases haHole :
      flipBoolWordAt word a ∉ coveredCompletionWords C
  · exact Or.inl ⟨a,ha,haHole⟩
  · by_cases hbHole :
      flipBoolWordAt word b ∉ coveredCompletionWords C
    · exact Or.inl ⟨b,hb,hbHole⟩
    · by_cases hcHole :
        flipBoolWordAt word c ∉ coveredCompletionWords C
      · exact Or.inl ⟨c,hc,hcHole⟩
      · have haCovered :
            flipBoolWordAt word a ∈ coveredCompletionWords C := by
          simpa using haHole
        have hbCovered :
            flipBoolWordAt word b ∈ coveredCompletionWords C := by
          simpa using hbHole
        have hcCovered :
            flipBoolWordAt word c ∈ coveredCompletionWords C := by
          simpa using hcHole
        have haNonempty :=
          (mem_coveredCompletionWords C
            (flipBoolWordAt word a)).1 haCovered
        have hbNonempty :=
          (mem_coveredCompletionWords C
            (flipBoolWordAt word b)).1 hbCovered
        have hcNonempty :=
          (mem_coveredCompletionWords C
            (flipBoolWordAt word c)).1 hcCovered

        by_cases hstrict :
            ∃ w : V,
              (
                w ∈ completionFibre C (flipBoolWordAt word a)
                ∨
                w ∈ completionFibre C (flipBoolWordAt word b)
                ∨
                w ∈ completionFibre C (flipBoolWordAt word c)
              ) ∧
              exponent w < projectedFree C w
        · right
          left
          obtain ⟨w,_hwF,hwStrict⟩ := hstrict
          exact ⟨w,
            projected_strict_surplus_at_least_one
              exponent (projectedFree C) hwStrict⟩
        · right
          right
          refine ⟨a,b,c,ha,hb,hc,hab,hac,hbc,
            haNonempty,hbNonempty,hcNonempty,
            completionFibre_card_le_two
              C (flipBoolWordAt word a),
            completionFibre_card_le_two
              C (flipBoolWordAt word b),
            completionFibre_card_le_two
              C (flipBoolWordAt word c),
            two_single_flips_have_disjoint_blocker_fibres
              C hsingle ha hb hab,
            two_single_flips_have_disjoint_blocker_fibres
              C hsingle ha hc hac,
            two_single_flips_have_disjoint_blocker_fibres
              C hsingle hb hc hbc,
            ?_⟩
          intro w hwF
          have hwNe : w ≠ v := by
            intro hwv
            subst w
            rcases hwF with hwa | hwb | hwc
            · exact
                (flip_active_not_mem_completion
                  C hword ha)
                ((mem_completionFibre
                  C (flipBoolWordAt word a) v).1 hwa)
            · exact
                (flip_active_not_mem_completion
                  C hword hb)
                ((mem_completionFibre
                  C (flipBoolWordAt word b) v).1 hwb)
            · exact
                (flip_active_not_mem_completion
                  C hword hc)
                ((mem_completionFibre
                  C (flipBoolWordAt word c) v).1 hwc)
          have hnotStrict :
              ¬ exponent w < projectedFree C w := by
            intro hs
            exact hstrict ⟨w,hwF,hs⟩
          rcases projectedProfile_strict_exact_or_loss
              C exponent hexp honeLoss w
            with hs | hexact | hloss
          · exact False.elim (hnotStrict hs)
          · exact ⟨hwNe,Or.inl hexact⟩
          · exact ⟨hwNe,Or.inr hloss⟩


theorem secondLayerLoss_word_closed_outlet_of_multiplicity
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexpLt : ∀ z, exponent z < n)
    (hexp : ∀ z, exponent z ≤ n)
    (honeLoss :
      ∀ z, (active C z).card ≤ n - exponent z + 1)
    (htop :
      ((Finset.univ : Finset V).filter
        (fun z => exponent z = n - 1)).card ≤ 1)
    (hsecond :
      ((Finset.univ : Finset V).filter
        (fun z => exponent z = n - 2)).card ≤ 2)
    {v : V}
    (hvLoss : v ∈ projectedLossVertices C exponent)
    (hvSecond : exponent v = n - 2)
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
        exponent w + 1 ≤ n - 2
    ) := by
  classical
  rcases
    secondLayerLoss_three_exit_hole_or_paid_or_disjoint_exact_loss_fibres
      C exponent hexp honeLoss
      hvLoss hvSecond hword
    with hhole | hpaid | hhard
  · exact Or.inl hhole
  · exact Or.inr (Or.inl hpaid)
  · obtain ⟨a,b,c,ha,hb,hc,hab,hac,hbc,
        haNonempty,hbNonempty,hcNonempty,
        _haCard,_hbCard,_hcCard,
        habDisj,hacDisj,hbcDisj,hprofile⟩ := hhard

    by_cases hexact :
        ∃ w : V,
          (
            w ∈ completionFibre C (flipBoolWordAt word a)
            ∨
            w ∈ completionFibre C (flipBoolWordAt word b)
            ∨
            w ∈ completionFibre C (flipBoolWordAt word c)
          ) ∧
          ExactProjectedBudget C exponent w
    · obtain ⟨w,_hwF,hwExact⟩ := hexact
      exact Or.inr (Or.inr (Or.inl ⟨w,hwExact⟩))

    · by_cases hdeep :
        ∃ w : V,
          (
            w ∈ completionFibre C (flipBoolWordAt word a)
            ∨
            w ∈ completionFibre C (flipBoolWordAt word b)
            ∨
            w ∈ completionFibre C (flipBoolWordAt word c)
          ) ∧
          w ∈ projectedLossVertices C exponent ∧
          exponent w + 1 ≤ n - 2
      · obtain ⟨w,_hwF,hwLoss,hwDeep⟩ := hdeep
        exact Or.inr (Or.inr (Or.inr
          ⟨w,hwLoss,hwDeep⟩))

      · have hhardLayer :
          ∀ w : V,
            (
              w ∈ completionFibre C (flipBoolWordAt word a)
              ∨
              w ∈ completionFibre C (flipBoolWordAt word b)
              ∨
              w ∈ completionFibre C (flipBoolWordAt word c)
            ) →
            w ∈ projectedLossVertices C exponent ∧
            (
              exponent w = n - 2
              ∨
              exponent w = n - 1
            ) := by
          intro w hwF
          have hwProfile := hprofile w hwF
          rcases hwProfile.2 with hwExact | hwLoss
          · exact False.elim
              (hexact ⟨w,hwF,hwExact⟩)
          · refine ⟨hwLoss,?_⟩
            have hwLt := hexpLt w
            by_contra hnot
            have hwDeep :
                exponent w + 1 ≤ n - 2 := by
              omega
            exact hdeep ⟨w,hwF,hwLoss,hwDeep⟩

        obtain ⟨wa,hwa⟩ := haNonempty
        obtain ⟨wb,hwb⟩ := hbNonempty
        obtain ⟨wc,hwc⟩ := hcNonempty

        have hwaLayer := hhardLayer wa (Or.inl hwa)
        have hwbLayer := hhardLayer wb (Or.inr (Or.inl hwb))
        have hwcLayer := hhardLayer wc (Or.inr (Or.inr hwc))

        have hwab : wa ≠ wb := by
          intro h
          subst wb
          exact Finset.disjoint_left.mp habDisj hwa hwb
        have hwac : wa ≠ wc := by
          intro h
          subst wc
          exact Finset.disjoint_left.mp hacDisj hwa hwc
        have hwbc : wb ≠ wc := by
          intro h
          subst wc
          exact Finset.disjoint_left.mp hbcDisj hwb hwc

        have hva : v ≠ wa := by
          exact (hprofile wa (Or.inl hwa)).1.symm
        have hvb : v ≠ wb := by
          exact (hprofile wb (Or.inr (Or.inl hwb))).1.symm
        have hvc : v ≠ wc := by
          exact (hprofile wc (Or.inr (Or.inr hwc))).1.symm

        have htopAtMostOne :
            ¬ (
              (exponent wa = n - 1 ∧ exponent wb = n - 1)
              ∨
              (exponent wa = n - 1 ∧ exponent wc = n - 1)
              ∨
              (exponent wb = n - 1 ∧ exponent wc = n - 1)
            ) := by
          intro hpairs
          rcases hpairs with habTop | hacTop | hbcTop
          · have hsub :
                ({wa,wb} : Finset V) ⊆
                  (Finset.univ : Finset V).filter
                    (fun z => exponent z = n - 1) := by
              intro z hz
              simp only [Finset.mem_insert, Finset.mem_singleton] at hz
              rcases hz with rfl | rfl
              · simp [habTop.1]
              · simp [habTop.2]
            have hcard :=
              Finset.card_le_card hsub
            have htwo : ({wa,wb} : Finset V).card = 2 := by
              simp [hwab]
            rw [htwo] at hcard
            omega
          · have hsub :
                ({wa,wc} : Finset V) ⊆
                  (Finset.univ : Finset V).filter
                    (fun z => exponent z = n - 1) := by
              intro z hz
              simp only [Finset.mem_insert, Finset.mem_singleton] at hz
              rcases hz with rfl | rfl
              · simp [hacTop.1]
              · simp [hacTop.2]
            have hcard := Finset.card_le_card hsub
            have htwo : ({wa,wc} : Finset V).card = 2 := by
              simp [hwac]
            rw [htwo] at hcard
            omega
          · have hsub :
                ({wb,wc} : Finset V) ⊆
                  (Finset.univ : Finset V).filter
                    (fun z => exponent z = n - 1) := by
              intro z hz
              simp only [Finset.mem_insert, Finset.mem_singleton] at hz
              rcases hz with rfl | rfl
              · simp [hbcTop.1]
              · simp [hbcTop.2]
            have hcard := Finset.card_le_card hsub
            have htwo : ({wb,wc} : Finset V).card = 2 := by
              simp [hwbc]
            rw [htwo] at hcard
            omega

        have htwoSecond :
            (
              exponent wa = n - 2 ∧ exponent wb = n - 2
            )
            ∨
            (
              exponent wa = n - 2 ∧ exponent wc = n - 2
            )
            ∨
            (
              exponent wb = n - 2 ∧ exponent wc = n - 2
            ) := by
          rcases hwaLayer.2 with hwaSecond | hwaTop <;>
            rcases hwbLayer.2 with hwbSecond | hwbTop <;>
              rcases hwcLayer.2 with hwcSecond | hwcTop
          · exact Or.inl ⟨hwaSecond,hwbSecond⟩
          · exact Or.inl ⟨hwaSecond,hwbSecond⟩
          · exact Or.inr (Or.inl ⟨hwaSecond,hwcSecond⟩)
          · exact False.elim
              (htopAtMostOne
                (Or.inr (Or.inr ⟨hwbTop,hwcTop⟩)))
          · exact Or.inr (Or.inr ⟨hwbSecond,hwcSecond⟩)
          · exact False.elim
              (htopAtMostOne
                (Or.inr (Or.inl ⟨hwaTop,hwcTop⟩)))
          · exact False.elim
              (htopAtMostOne
                (Or.inl ⟨hwaTop,hwbTop⟩))
          · exact False.elim
              (htopAtMostOne
                (Or.inl ⟨hwaTop,hwbTop⟩))

        have hthreeSecond :
            ∃ x y : V,
              x ≠ y ∧
              v ≠ x ∧ v ≠ y ∧
              exponent x = n - 2 ∧
              exponent y = n - 2 := by
          rcases htwoSecond with habSecond | hacSecond | hbcSecond
          · exact ⟨wa,wb,hwab,hva,hvb,habSecond.1,habSecond.2⟩
          · exact ⟨wa,wc,hwac,hva,hvc,hacSecond.1,hacSecond.2⟩
          · exact ⟨wb,wc,hwbc,hvb,hvc,hbcSecond.1,hbcSecond.2⟩

        obtain ⟨x,y,hxy,hvx,hvy,hxSecond,hySecond⟩ := hthreeSecond
        have hsub :
            ({v,x,y} : Finset V) ⊆
              (Finset.univ : Finset V).filter
                (fun z => exponent z = n - 2) := by
          intro z hz
          simp only [Finset.mem_insert, Finset.mem_singleton] at hz
          rcases hz with rfl | rfl | rfl
          · simp [hvSecond]
          · simp [hxSecond]
          · simp [hySecond]
        have hcard := Finset.card_le_card hsub
        have hthree : ({v,x,y} : Finset V).card = 3 := by
          simp [hvx,hvy,hxy]
        rw [hthree] at hcard
        omega

#print axioms secondLayerLoss_word_closed_outlet_of_multiplicity

end OrderedEdgeColoring
end JSP000404Research
