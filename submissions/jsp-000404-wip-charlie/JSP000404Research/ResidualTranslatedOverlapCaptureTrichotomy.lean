import JSP000404Research.ResidualTranslatedOverlapFullCapture
import JSP000404Research.ResidualTranslatedOverlapHalfCapture
import JSP000404Research.ResidualTranslatedOverlapHalfCaptureTwo
import Mathlib.Tactic

/-!
# Exact blocker-capture trichotomy

For one- or two-bit pair-local translations of an overlap cube, every fixed
blocker has one of only three possible capture regimes:

* captures nothing;
* captures the whole translated overlap cube;
* captures at most half of it.

The full case occurs precisely through full inheritance of the common-inactive
directions; otherwise the pairing argument gives the factor-two loss.
-/

namespace JSP000404Research
namespace OrderedEdgeColoring

theorem oneFlip_capture_zero_full_or_half
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    {u v w : V} {c : Fin n}
    (hc : c ∈ retainedActive C u) :
    (oneFlipCapturedSourceWords C u v w c).card = 0
    ∨
    (oneFlipCapturedSourceWords C u v w c).card =
      (retainedCompletionWords C u ∩
        retainedCompletionWords C v).card
    ∨
    2 * (oneFlipCapturedSourceWords C u v w c).card ≤
      (retainedCompletionWords C u ∩
        retainedCompletionWords C v).card := by
  classical
  by_cases hzero :
      (oneFlipCapturedSourceWords C u v w c).card = 0
  · exact Or.inl hzero
  · right
    have hnonempty :
        (oneFlipCapturedSourceWords C u v w c).Nonempty :=
      Finset.card_pos.mp (Nat.pos_of_ne_zero hzero)
    obtain ⟨base,hbaseCap⟩ := hnonempty
    have hbaseData :=
      (mem_oneFlipCapturedSourceWords
        C u v w c base).1 hbaseCap
    rcases oneFlip_blocker_fullFree_or_halfCapture C hc
      with hfull | hhalf
    · left
      let f :
          {word // word ∈ oneFlipCapturedSourceWords C u v w c} ≃
          {word // word ∈
            retainedCompletionWords C u ∩ retainedCompletionWords C v} :=
        Equiv.ofBijective
          (fun word => ⟨word.1,
            ((mem_oneFlipCapturedSourceWords
              C u v w c word.1).1 word.2).1⟩)
          ⟨
            by
              intro x y hxy
              apply Subtype.ext
              exact congrArg
                (fun q :
                  {word : Fin n → Bool //
                    word ∈ retainedCompletionWords C u ∩
                      retainedCompletionWords C v} => q.1)
                hxy,
            by
              intro word
              have hfullCapture :=
                oneFlip_fullFree_nonempty_capture_is_full
                  C hfull hbaseData.1 hbaseData.2
              refine ⟨⟨word.1, ?_⟩, rfl⟩
              apply (mem_oneFlipCapturedSourceWords
                C u v w c word.1).2
              exact ⟨word.2,hfullCapture word.1 word.2⟩
          ⟩
      have hcard := Fintype.card_congr f
      simpa only [Fintype.card_coe] using hcard
    · exact Or.inr hhalf

theorem twoFlip_capture_zero_full_or_half
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    {u v w : V} {c d : Fin n}
    (hc : c ∈ retainedActive C u)
    (hd : d ∈ retainedActive C v) :
    (twoFlipCapturedSourceWords C u v w c d).card = 0
    ∨
    (twoFlipCapturedSourceWords C u v w c d).card =
      (retainedCompletionWords C u ∩
        retainedCompletionWords C v).card
    ∨
    2 * (twoFlipCapturedSourceWords C u v w c d).card ≤
      (retainedCompletionWords C u ∩
        retainedCompletionWords C v).card := by
  classical
  by_cases hzero :
      (twoFlipCapturedSourceWords C u v w c d).card = 0
  · exact Or.inl hzero
  · right
    have hnonempty :
        (twoFlipCapturedSourceWords C u v w c d).Nonempty :=
      Finset.card_pos.mp (Nat.pos_of_ne_zero hzero)
    obtain ⟨base,hbaseCap⟩ := hnonempty
    have hbaseData :=
      (mem_twoFlipCapturedSourceWords
        C u v w c d base).1 hbaseCap
    rcases twoFlip_blocker_fullFree_or_halfCapture C hc hd
      with hfull | hhalf
    · left
      let f :
          {word // word ∈ twoFlipCapturedSourceWords C u v w c d} ≃
          {word // word ∈
            retainedCompletionWords C u ∩ retainedCompletionWords C v} :=
        Equiv.ofBijective
          (fun word => ⟨word.1,
            ((mem_twoFlipCapturedSourceWords
              C u v w c d word.1).1 word.2).1⟩)
          ⟨
            by
              intro x y hxy
              apply Subtype.ext
              exact congrArg
                (fun q :
                  {word : Fin n → Bool //
                    word ∈ retainedCompletionWords C u ∩
                      retainedCompletionWords C v} => q.1)
                hxy,
            by
              intro word
              have hfullCapture :=
                twoFlip_fullFree_nonempty_capture_is_full
                  C hfull hbaseData.1 hbaseData.2
              refine ⟨⟨word.1, ?_⟩, rfl⟩
              apply (mem_twoFlipCapturedSourceWords
                C u v w c d word.1).2
              exact ⟨word.2,hfullCapture word.1 word.2⟩
          ⟩
      have hcard := Fintype.card_congr f
      simpa only [Fintype.card_coe] using hcard
    · exact Or.inr hhalf

#print axioms oneFlip_capture_zero_full_or_half
#print axioms twoFlip_capture_zero_full_or_half

end OrderedEdgeColoring
end JSP000404Research
