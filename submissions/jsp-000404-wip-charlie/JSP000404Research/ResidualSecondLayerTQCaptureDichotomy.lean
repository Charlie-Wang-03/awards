import JSP000404Research.ResidualSamePaletteCubeAmplification
import JSP000404Research.ResidualTranslatedFlipExclusion
import JSP000404Research.ResidualSecondLayerProjectedLossCard
import Mathlib.Tactic

/-!
# Second-layer T/Q collision: whole-cube rematch or half capture

Let v,w be projected-loss second-layer vertices and let d be active at both.
Assume the translated slice T_d(v) meets the completion cube Q_w.

Both retained-active palettes have cardinality three.

* If the palettes are equal, one-point intersection amplifies to the exact
  whole-cube identity T_d(v)=Q_w.
* If the palettes differ, choose e active at v but inactive at w.  Since d is
  active at w, e != d.  For every captured source word y, flip_e(y) remains in
  Q_w but exits T_d(v).  Thus captured words pair injectively with disjoint
  partner words inside Q_w, giving a factor-two capture bound.

This is the exact full-rematch / half-capture dichotomy required by the
weighted recursion.
-/

namespace JSP000404Research
namespace OrderedEdgeColoring

noncomputable def translatedBaseCapture
    {V : Type*} [LinearOrder V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (v w : V) (d : Fin n) : Finset (Fin n → Bool) :=
  translatedCompletionWords C v d ∩ retainedCompletionWords C w

theorem translatedBaseCapture_half_of_missing_source_active
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    {v w : V} {d e : Fin n}
    (hdV : d ∈ retainedActive C v)
    (heV : e ∈ retainedActive C v)
    (hed : e ≠ d)
    (heW : e ∉ retainedActive C w) :
    2 * (translatedBaseCapture C v w d).card
      ≤ (retainedCompletionWords C w).card := by
  classical
  let S := translatedBaseCapture C v w d
  let F := S.image (fun word => flipBoolWordAt word e)

  have hFcard : F.card = S.card := by
    dsimp [F]
    rw [Finset.card_image_iff.mpr]
    intro a ha b hb hab
    exact flipBoolWordAt_injective e hab

  have hsubS :
      S ⊆ retainedCompletionWords C w := by
    intro word hword
    exact (Finset.mem_inter.mp hword).2

  have hsubF :
      F ⊆ retainedCompletionWords C w := by
    intro z hz
    obtain ⟨word,hwordS,rfl⟩ := Finset.mem_image.mp hz
    have hwQ := (Finset.mem_inter.mp hwordS).2
    exact (mem_retainedCompletionWords_flip_iff_of_inactive C heW).2 hwQ

  have hdisj : Disjoint S F := by
    rw [Finset.disjoint_left]
    intro word hwordS hwordF
    obtain ⟨base,hbaseS,hflipEq⟩ :=
      Finset.mem_image.mp hwordF
    have hwordT :=
      (Finset.mem_inter.mp hwordS).1
    have hbaseT :=
      (Finset.mem_inter.mp hbaseS).1
    rw [← hflipEq] at hwordT
    exact flip_other_active_not_mem_translated
      C heV hed hbaseT hwordT

  have hunionSub :
      S ∪ F ⊆ retainedCompletionWords C w := by
    intro word hword
    rcases Finset.mem_union.mp hword with hs | hf
    · exact hsubS hs
    · exact hsubF hf

  have hcard := Finset.card_le_card hunionSub
  rw [Finset.card_union_of_disjoint hdisj,hFcard] at hcard
  simpa [S, two_mul] using hcard

theorem secondLayer_TQ_wholeCube_or_halfCapture
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hn3 : 3 ≤ n)
    {v w : V} {d : Fin n}
    (hvLoss : v ∈ projectedLossVertices C exponent)
    (hwLoss : w ∈ projectedLossVertices C exponent)
    (hvSecond : exponent v = n - 2)
    (hwSecond : exponent w = n - 2)
    (hdV : d ∈ retainedActive C v)
    (hdW : d ∈ retainedActive C w)
    (hinter :
      (translatedCompletionWords C v d ∩
        retainedCompletionWords C w).Nonempty) :
    WholeCubeQTPair C w v d
    ∨
    2 * (translatedBaseCapture C v w d).card
      ≤ (retainedCompletionWords C w).card := by
  have hvCard :
      (retainedActive C v).card = 3 :=
    secondLayer_projectedLoss_retainedActive_card_eq_three_core
      C exponent hvLoss hvSecond
  have hwCard :
      (retainedActive C w).card = 3 :=
    secondLayer_projectedLoss_retainedActive_card_eq_three_core
      C exponent hwLoss hwSecond

  by_cases hEq :
      retainedActive C v = retainedActive C w
  · left
    exact wholeCubeQTPair_of_same_palette_translated_intersection
      C hEq hdV hinter
  · right
    have hnotSub :
        ¬ retainedActive C v ⊆ retainedActive C w := by
      intro hsub
      have hcardLe :=
        Finset.card_le_card hsub
      have hEq' :
          retainedActive C v = retainedActive C w :=
        Finset.eq_of_subset_of_card_le
          hsub (by simpa [hvCard,hwCard])
      exact hEq hEq'
    obtain ⟨e,heV,heW⟩ :=
      Finset.not_subset.mp hnotSub
    have hed : e ≠ d := by
      intro hed
      subst e
      exact heW hdW
    exact translatedBaseCapture_half_of_missing_source_active
      C hdV heV hed heW

theorem secondLayer_TQ_wholeCube_or_half_source_cube
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hn3 : 3 ≤ n)
    {v w : V} {d : Fin n}
    (hvLoss : v ∈ projectedLossVertices C exponent)
    (hwLoss : w ∈ projectedLossVertices C exponent)
    (hvSecond : exponent v = n - 2)
    (hwSecond : exponent w = n - 2)
    (hdV : d ∈ retainedActive C v)
    (hdW : d ∈ retainedActive C w)
    (hinter :
      (translatedCompletionWords C v d ∩
        retainedCompletionWords C w).Nonempty) :
    WholeCubeQTPair C w v d
    ∨
    2 * (translatedBaseCapture C v w d).card
      ≤ (retainedCompletionWords C v).card := by
  rcases secondLayer_TQ_wholeCube_or_halfCapture
      C exponent hn3
      hvLoss hwLoss hvSecond hwSecond
      hdV hdW hinter
    with hwhole | hhalf
  · exact Or.inl hwhole
  · right
    have hvCard :
        (retainedActive C v).card = 3 :=
      secondLayer_projectedLoss_retainedActive_card_eq_three_core
        C exponent hvLoss hvSecond
    have hwCard :
        (retainedActive C w).card = 3 :=
      secondLayer_projectedLoss_retainedActive_card_eq_three_core
        C exponent hwLoss hwSecond
    rw [retainedCompletionWords_card, hwCard] at hhalf
    rw [retainedCompletionWords_card, hvCard]
    exact hhalf

#print axioms translatedBaseCapture_half_of_missing_source_active
#print axioms secondLayer_TQ_wholeCube_or_halfCapture
#print axioms secondLayer_TQ_wholeCube_or_half_source_cube

end OrderedEdgeColoring
end JSP000404Research
