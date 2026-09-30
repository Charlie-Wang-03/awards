import JSP000404Research.ResidualTranslatedOverlapFreeInheritance
import Mathlib.Tactic

/-!
# Half-capture bound for a blocker active on a common-inactive direction

Fix an overlap carrier u,v, a one-coordinate pair displacement c, and a third
blocker w.  Let S be the source overlap words whose displaced images land in
Q_w.

If e is common-inactive at u,v but active at w, then flipping e pairs every
captured source word with another source overlap word whose displaced image
cannot also lie in Q_w.  Hence

  2 * card(S) <= card(Q_u ∩ Q_v).

This is the first quantitative cross-carrier collision bound: a blocker which
fails to inherit one internal overlap direction can capture at most half of the
translated overlap cube.
-/

namespace JSP000404Research
namespace OrderedEdgeColoring

noncomputable def oneFlipCapturedSourceWords
    {V : Type*} [LinearOrder V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (u v w : V) (c : Fin n) :
    Finset (Fin n → Bool) := by
  classical
  exact
    (retainedCompletionWords C u ∩
      retainedCompletionWords C v).filter
      (fun word =>
        flipBoolWordAt word c ∈ retainedCompletionWords C w)

@[simp] theorem mem_oneFlipCapturedSourceWords
    {V : Type*} [LinearOrder V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (u v w : V) (c : Fin n)
    (word : Fin n → Bool) :
    word ∈ oneFlipCapturedSourceWords C u v w c ↔
      word ∈ retainedCompletionWords C u ∩
        retainedCompletionWords C v ∧
      flipBoolWordAt word c ∈ retainedCompletionWords C w := by
  classical
  simp [oneFlipCapturedSourceWords]

theorem two_mul_oneFlipCaptured_le_overlap_of_commonInactive_active
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    {u v w : V} {c e : Fin n}
    (heCommon : e ∈ commonInactiveRetained C u v)
    (hc : c ∈ retainedActive C u)
    (heW : e ∈ retainedActive C w) :
    2 * (oneFlipCapturedSourceWords C u v w c).card ≤
      (retainedCompletionWords C u ∩
        retainedCompletionWords C v).card := by
  classical
  let source :=
    retainedCompletionWords C u ∩ retainedCompletionWords C v
  let captured :=
    oneFlipCapturedSourceWords C u v w c
  have hcapSub : captured ⊆ source := by
    intro word hword
    exact
      (mem_oneFlipCapturedSourceWords
        C u v w c word).1 hword |>.1
  let target := source  captured

  have heData :=
    (mem_commonInactiveRetained C u v e).1 heCommon
  have heU : e ∉ retainedActive C u := heData.1
  have heV : e ∉ retainedActive C v := heData.2

  let f : {word // word ∈ captured} →
      {word // word ∈ target} :=
    fun word => ⟨flipBoolWordAt word.1 e, by
      have hwordData :=
        (mem_oneFlipCapturedSourceWords
          C u v w c word.1).1 word.2
      have hsource := hwordData.1
      have hu := (Finset.mem_inter.mp hsource).1
      have hv := (Finset.mem_inter.mp hsource).2
      have huFlip :
          flipBoolWordAt word.1 e ∈
            retainedCompletionWords C u :=
        (mem_completion_iff_flip_of_inactive C heU).2 hu
      have hvFlip :
          flipBoolWordAt word.1 e ∈
            retainedCompletionWords C v :=
        (mem_completion_iff_flip_of_inactive C heV).2 hv
      have hsourceFlip :
          flipBoolWordAt word.1 e ∈ source := by
        exact Finset.mem_inter.mpr ⟨huFlip,hvFlip⟩
      have hnotCaptured :
          flipBoolWordAt word.1 e ∉ captured := by
        intro hcapt
        have hcaptData :=
          (mem_oneFlipCapturedSourceWords
            C u v w c (flipBoolWordAt word.1 e)).1 hcapt
        have heInactive :=
          blocker_inherits_commonInactive_of_one_flip_pair
            C heCommon hc hwordData.2 hcaptData.2
        exact heInactive heW
      exact Finset.mem_sdiff.mpr ⟨hsourceFlip,hnotCaptured⟩⟩

  have hf : Function.Injective f := by
    intro x y hxy
    apply Subtype.ext
    apply flipBoolWordAt_injective e
    exact congrArg Subtype.val hxy

  have hcard :
      captured.card ≤ target.card := by
    simpa only [Fintype.card_coe] using
      (Fintype.card_le_of_injective f hf)

  have hsplit :
      target.card + captured.card = source.card := by
    dsimp [target]
    exact Finset.card_sdiff_add_card_eq_card hcapSub

  dsimp [captured, source] at hcard hsplit ⊢
  omega

#print axioms two_mul_oneFlipCaptured_le_overlap_of_commonInactive_active

end OrderedEdgeColoring
end JSP000404Research
