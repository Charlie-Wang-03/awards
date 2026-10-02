import JSP000404Research.ResidualWholeCubeSecondCoordinateCollision
import JSP000404Research.ResidualSecondLayerTQCaptureDichotomy
import JSP000404Research.ResidualTranslatedOverlapFreeInheritance
import Mathlib.Tactic

/-!
# Second-layer T/T collision: full translated rematch or half capture

A translated slice is itself a Boolean subcube on the same retained-active
coordinate set as its source completion cube, with one virtual retained bit
toggled at the translation coordinate.

Therefore two translated slices with the same active palette are either
disjoint or equal.  If their palettes differ, a source-active coordinate
missing from the target palette pairs every captured source word with a
distinct target word outside the source slice, giving factor-two decay.
-/

namespace JSP000404Research
namespace OrderedEdgeColoring

noncomputable def translatedRetainedBit
    {V : Type*} [LinearOrder V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (v : V) (d q : Fin n) : Bool :=
  if q = d then !(retainedBit C v q) else retainedBit C v q

theorem mem_translatedCompletionWords_iff_translatedRetainedBit
    {V : Type*} [LinearOrder V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (v : V) (d : Fin n) (word : Fin n → Bool) :
    word ∈ translatedCompletionWords C v d ↔
      ∀ q, q ∈ retainedActive C v →
        word q = translatedRetainedBit C v d q := by
  rw [mem_translatedCompletionWords]
  constructor
  · intro hbase q hq
    have h :=
      (mem_retainedCompletionWords C v
        (flipBoolWordAt word d)).1 hbase q hq
    by_cases hqd : q = d
    · subst q
      rw [flipBoolWordAt_at] at h
      simp [translatedRetainedBit, h]
    · rw [flipBoolWordAt_off word hqd] at h
      simpa [translatedRetainedBit, hqd] using h
  · intro hbits
    apply (mem_retainedCompletionWords C v
      (flipBoolWordAt word d)).2
    intro q hq
    have h := hbits q hq
    by_cases hqd : q = d
    · subst q
      simp [translatedRetainedBit] at h ⊢
      cases hb : retainedBit C v d <;>
        cases hw : word d <;>
        simp_all
    · rw [flipBoolWordAt_off word hqd]
      simpa [translatedRetainedBit, hqd] using h

theorem translatedCompletionWords_eq_of_same_palette_nonempty_inter
    {V : Type*} [LinearOrder V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    {v w : V} {d e : Fin n}
    (hactive :
      retainedActive C v = retainedActive C w)
    (hinter :
      (translatedCompletionWords C v d ∩
        translatedCompletionWords C w e).Nonempty) :
    translatedCompletionWords C v d =
      translatedCompletionWords C w e := by
  obtain ⟨base,hbaseV,hbaseW⟩ :=
    Finset.nonempty_inter.mp hinter
  have hvBase :=
    (mem_translatedCompletionWords_iff_translatedRetainedBit
      C v d base).1 hbaseV
  have hwBase :=
    (mem_translatedCompletionWords_iff_translatedRetainedBit
      C w e base).1 hbaseW
  have hpattern :
      ∀ q, q ∈ retainedActive C v →
        translatedRetainedBit C v d q =
          translatedRetainedBit C w e q := by
    intro q hqV
    have hqW : q ∈ retainedActive C w := by
      rw [← hactive]
      exact hqV
    exact (hvBase q hqV).symm.trans (hwBase q hqW)
  ext word
  rw [mem_translatedCompletionWords_iff_translatedRetainedBit,
      mem_translatedCompletionWords_iff_translatedRetainedBit]
  constructor
  · intro hv q hqW
    have hqV : q ∈ retainedActive C v := by
      rw [hactive]
      exact hqW
    exact (hv q hqV).trans (hpattern q hqV)
  · intro hw q hqV
    have hqW : q ∈ retainedActive C w := by
      rw [← hactive]
      exact hqV
    exact (hw q hqW).trans (hpattern q hqV).symm

theorem mem_translated_iff_flip_of_inactive
    {V : Type*} [LinearOrder V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    {w : V} {word : Fin n → Bool}
    {e f : Fin n}
    (heW : e ∈ retainedActive C w)
    (hfW : f ∉ retainedActive C w) :
    flipBoolWordAt word f ∈ translatedCompletionWords C w e
      ↔
    word ∈ translatedCompletionWords C w e := by
  have hfe : f ≠ e := by
    intro h
    subst f
    exact hfW heW
  rw [mem_translatedCompletionWords,
      mem_translatedCompletionWords]
  rw [flipBoolWordAt_commute word hfe]
  exact mem_completion_iff_flip_of_inactive C hfW

theorem flip_active_not_mem_same_translated
    {V : Type*} [LinearOrder V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    {v : V} {word : Fin n → Bool}
    {d f : Fin n}
    (hdV : d ∈ retainedActive C v)
    (hfV : f ∈ retainedActive C v)
    (hword : word ∈ translatedCompletionWords C v d) :
    flipBoolWordAt word f ∉ translatedCompletionWords C v d := by
  by_cases hfd : f = d
  · subst f
    intro hflipT
    have hbase :
        flipBoolWordAt word d ∈ retainedCompletionWords C v :=
      (mem_translatedCompletionWords C v d word).1 hword
    have hdisj :=
      translatedCompletionWords_disjoint_original_of_active C hdV
    exact Finset.disjoint_left.mp hdisj hflipT hbase
  · exact flip_other_active_not_mem_translated
      C hfV hfd hword

noncomputable def translatedTranslatedCapture
    {V : Type*} [LinearOrder V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (v w : V) (d e : Fin n) : Finset (Fin n → Bool) :=
  translatedCompletionWords C v d ∩
    translatedCompletionWords C w e

theorem translatedTranslatedCapture_half_of_missing_source_active
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    {v w : V} {d e f : Fin n}
    (hdV : d ∈ retainedActive C v)
    (heW : e ∈ retainedActive C w)
    (hfV : f ∈ retainedActive C v)
    (hfW : f ∉ retainedActive C w) :
    2 * (translatedTranslatedCapture C v w d e).card
      ≤ (translatedCompletionWords C w e).card := by
  classical
  let S := translatedTranslatedCapture C v w d e
  let F := S.image (fun word => flipBoolWordAt word f)
  have hFcard : F.card = S.card := by
    dsimp [F]
    rw [Finset.card_image_iff.mpr]
    intro a ha b hb hab
    exact flipBoolWordAt_injective f hab
  have hsubS :
      S ⊆ translatedCompletionWords C w e := by
    intro word hword
    exact (Finset.mem_inter.mp hword).2
  have hsubF :
      F ⊆ translatedCompletionWords C w e := by
    intro z hz
    obtain ⟨word,hwordS,rfl⟩ := Finset.mem_image.mp hz
    have hwT := (Finset.mem_inter.mp hwordS).2
    exact (mem_translated_iff_flip_of_inactive
      C heW hfW).2 hwT
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
    exact flip_active_not_mem_same_translated
      C hdV hfV hbaseT hwordT
  have hunionSub :
      S ∪ F ⊆ translatedCompletionWords C w e := by
    intro word hword
    rcases Finset.mem_union.mp hword with hs | hf
    · exact hsubS hs
    · exact hsubF hf
  have hcard := Finset.card_le_card hunionSub
  rw [Finset.card_union_of_disjoint hdisj,hFcard] at hcard
  omega

theorem secondLayer_TT_fullRematch_or_halfCapture
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    {v w : V} {d e : Fin n}
    (hvLoss : v ∈ projectedLossVertices C exponent)
    (hwLoss : w ∈ projectedLossVertices C exponent)
    (hvSecond : exponent v = n - 2)
    (hwSecond : exponent w = n - 2)
    (hdV : d ∈ retainedActive C v)
    (heW : e ∈ retainedActive C w)
    (hinter :
      (translatedCompletionWords C v d ∩
        translatedCompletionWords C w e).Nonempty) :
    translatedCompletionWords C v d =
        translatedCompletionWords C w e
    ∨
    2 * (translatedTranslatedCapture C v w d e).card
      ≤ (translatedCompletionWords C v d).card := by
  have hvCard :
      (retainedActive C v).card = 3 :=
    secondLayerLoss_retainedActive_card_eq_three
      C exponent hvLoss hvSecond
  have hwCard :
      (retainedActive C w).card = 3 :=
    secondLayerLoss_retainedActive_card_eq_three
      C exponent hwLoss hwSecond
  by_cases hEq :
      retainedActive C v = retainedActive C w
  · exact Or.inl
      (translatedCompletionWords_eq_of_same_palette_nonempty_inter
        C hEq hinter)
  · right
    have hnotSub :
        ¬ retainedActive C v ⊆ retainedActive C w := by
      intro hsub
      have hEq' :
          retainedActive C v = retainedActive C w :=
        Finset.eq_of_subset_of_card_le
          hsub (by simpa [hvCard,hwCard])
      exact hEq hEq'
    obtain ⟨f,hfV,hfW⟩ :=
      Finset.not_subset.mp hnotSub
    have hhalf :=
      translatedTranslatedCapture_half_of_missing_source_active
        C hdV heW hfV hfW
    rw [translatedCompletionWords_card,
        translatedCompletionWords_card] at hhalf ⊢
    exact hhalf

#print axioms mem_translatedCompletionWords_iff_translatedRetainedBit
#print axioms translatedCompletionWords_eq_of_same_palette_nonempty_inter
#print axioms translatedTranslatedCapture_half_of_missing_source_active
#print axioms secondLayer_TT_fullRematch_or_halfCapture

end OrderedEdgeColoring
end JSP000404Research
