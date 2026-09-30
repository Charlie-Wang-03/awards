import JSP000404Research.ResidualCompletionFibreLabel
import JSP000404Research.ResidualTranslatedOverlapHalfCapture
import JSP000404Research.ResidualTranslatedOverlapHalfCaptureTwo
import Mathlib.Tactic

/-!
# Global blocker-incidence bound for a fixed pair translation

For a fixed overlap pair and a fixed one- or two-bit translation, count blocker
incidences (source word, blocker vertex).

Map each incidence to

  (source word, residual bit of blocker).

For a fixed translated word the residual bit labels its completion fibre
injectively, so this map is injective.  Therefore the total blocker incidence
mass is at most twice the source overlap mass.
-/

namespace JSP000404Research
namespace OrderedEdgeColoring

abbrev OneFlipBlockerIncidence
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (u v : V) (c : Fin n) :=
  Σ w : V,
    {word : Fin n → Bool //
      word ∈ oneFlipCapturedSourceWords C u v w c}

abbrev TwoFlipBlockerIncidence
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (u v : V) (c d : Fin n) :=
  Σ w : V,
    {word : Fin n → Bool //
      word ∈ twoFlipCapturedSourceWords C u v w c d}

theorem oneFlip_blocker_incidence_injective
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (u v : V) (c : Fin n) :
    Function.Injective
      (fun z : OneFlipBlockerIncidence C u v c =>
        (
          (⟨z.2.1,
            ((mem_oneFlipCapturedSourceWords
              C u v z.1 c z.2.1).1 z.2.2).1⟩ :
            {word : Fin n → Bool //
              word ∈ retainedCompletionWords C u ∩
                retainedCompletionWords C v}),
          bit C z.1 (residualCoord n)
        )) := by
  intro x y hxy
  cases x with
  | mk wx xx =>
      cases y with
      | mk wy yy =>
          have hwordSub :
              (⟨xx.1,
                ((mem_oneFlipCapturedSourceWords
                  C u v wx c xx.1).1 xx.2).1⟩ :
                {word : Fin n → Bool //
                  word ∈ retainedCompletionWords C u ∩
                    retainedCompletionWords C v})
              =
              ⟨yy.1,
                ((mem_oneFlipCapturedSourceWords
                  C u v wy c yy.1).1 yy.2).1⟩ :=
            congrArg Prod.fst hxy
          have hword : xx.1 = yy.1 :=
            congrArg Subtype.val hwordSub
          have hbit :
              bit C wx (residualCoord n) =
                bit C wy (residualCoord n) :=
            congrArg Prod.snd hxy
          have hxData :=
            (mem_oneFlipCapturedSourceWords
              C u v wx c xx.1).1 xx.2
          have hyData0 :=
            (mem_oneFlipCapturedSourceWords
              C u v wy c yy.1).1 yy.2
          have hyComp :
              flipBoolWordAt xx.1 c ∈
                retainedCompletionWords C wy := by
            simpa [hword] using hyData0.2
          have hwEq :
              wx = wy :=
            completion_carriers_eq_of_residualBit_eq
              C hxData.2 hyComp hbit
          subst wy
          apply Sigma.ext rfl
          apply Subtype.ext
          exact hword

theorem twoFlip_blocker_incidence_injective
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (u v : V) (c d : Fin n) :
    Function.Injective
      (fun z : TwoFlipBlockerIncidence C u v c d =>
        (
          (⟨z.2.1,
            ((mem_twoFlipCapturedSourceWords
              C u v z.1 c d z.2.1).1 z.2.2).1⟩ :
            {word : Fin n → Bool //
              word ∈ retainedCompletionWords C u ∩
                retainedCompletionWords C v}),
          bit C z.1 (residualCoord n)
        )) := by
  intro x y hxy
  cases x with
  | mk wx xx =>
      cases y with
      | mk wy yy =>
          have hwordSub :
              (⟨xx.1,
                ((mem_twoFlipCapturedSourceWords
                  C u v wx c d xx.1).1 xx.2).1⟩ :
                {word : Fin n → Bool //
                  word ∈ retainedCompletionWords C u ∩
                    retainedCompletionWords C v})
              =
              ⟨yy.1,
                ((mem_twoFlipCapturedSourceWords
                  C u v wy c d yy.1).1 yy.2).1⟩ :=
            congrArg Prod.fst hxy
          have hword : xx.1 = yy.1 :=
            congrArg Subtype.val hwordSub
          have hbit :
              bit C wx (residualCoord n) =
                bit C wy (residualCoord n) :=
            congrArg Prod.snd hxy
          have hxData :=
            (mem_twoFlipCapturedSourceWords
              C u v wx c d xx.1).1 xx.2
          have hyData0 :=
            (mem_twoFlipCapturedSourceWords
              C u v wy c d yy.1).1 yy.2
          have hyComp :
              flipBoolWordAt (flipBoolWordAt xx.1 c) d ∈
                retainedCompletionWords C wy := by
            simpa [hword] using hyData0.2
          have hwEq :
              wx = wy :=
            completion_carriers_eq_of_residualBit_eq
              C hxData.2 hyComp hbit
          subst wy
          apply Sigma.ext rfl
          apply Subtype.ext
          exact hword

theorem sum_oneFlip_blocker_capture_le_two_mul_overlap
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (u v : V) (c : Fin n) :
    (∑ w : V, (oneFlipCapturedSourceWords C u v w c).card)
      ≤
    2 * (retainedCompletionWords C u ∩
      retainedCompletionWords C v).card := by
  classical
  let f :
      OneFlipBlockerIncidence C u v c →
        ({word : Fin n → Bool //
          word ∈ retainedCompletionWords C u ∩
            retainedCompletionWords C v}) × Bool :=
    fun z =>
      (
        ⟨z.2.1,
          ((mem_oneFlipCapturedSourceWords
            C u v z.1 c z.2.1).1 z.2.2).1⟩,
        bit C z.1 (residualCoord n)
      )
  have hf : Function.Injective f :=
    oneFlip_blocker_incidence_injective C u v c
  have hcard :=
    Fintype.card_le_of_injective f hf
  rw [Fintype.card_sigma] at hcard
  simpa [Fintype.card_prod, Fintype.card_coe, Nat.mul_comm] using hcard

theorem sum_twoFlip_blocker_capture_le_two_mul_overlap
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (u v : V) (c d : Fin n) :
    (∑ w : V, (twoFlipCapturedSourceWords C u v w c d).card)
      ≤
    2 * (retainedCompletionWords C u ∩
      retainedCompletionWords C v).card := by
  classical
  let f :
      TwoFlipBlockerIncidence C u v c d →
        ({word : Fin n → Bool //
          word ∈ retainedCompletionWords C u ∩
            retainedCompletionWords C v}) × Bool :=
    fun z =>
      (
        ⟨z.2.1,
          ((mem_twoFlipCapturedSourceWords
            C u v z.1 c d z.2.1).1 z.2.2).1⟩,
        bit C z.1 (residualCoord n)
      )
  have hf : Function.Injective f :=
    twoFlip_blocker_incidence_injective C u v c d
  have hcard :=
    Fintype.card_le_of_injective f hf
  rw [Fintype.card_sigma] at hcard
  simpa [Fintype.card_prod, Fintype.card_coe, Nat.mul_comm] using hcard

#print axioms sum_oneFlip_blocker_capture_le_two_mul_overlap
#print axioms sum_twoFlip_blocker_capture_le_two_mul_overlap

end OrderedEdgeColoring
end JSP000404Research
