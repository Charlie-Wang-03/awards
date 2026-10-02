import JSP000404Research.ResidualWholeCubeTwoFlipCube
import JSP000404Research.ResidualWholeCubePartnerDistinct
import JSP000404Research.ResidualLossAllActiveCandidateBlock
import Mathlib.Tactic

/-!
# Seven-cube cover for three whole-cube partners

Fix a second-layer source v with retained-active palette {c1,c2,c3}. Suppose
there are three WholeCubeQTPair partners s1,s2,s3 attached at those three
coordinates.

Relative to Q_v, every enlarged all-active block of v,s1,s2,s3 is contained
in the union of exactly seven completion-type cubes:

* Q_v;
* the three one-flip cubes T_c1(v), T_c2(v), T_c3(v);
* the three two-flip cubes at {c1,c2}, {c1,c3}, {c2,c3}.

The missing eighth pattern is the triple flip.
-/

namespace JSP000404Research
namespace OrderedEdgeColoring

noncomputable def sevenCubeUnion
    {V : Type*} [LinearOrder V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (v : V) (c₁ c₂ c₃ : Fin n) : Finset (Fin n → Bool) :=
  retainedCompletionWords C v ∪
  translatedCompletionWords C v c₁ ∪
  translatedCompletionWords C v c₂ ∪
  translatedCompletionWords C v c₃ ∪
  twoFlipCompletionWords C v c₁ c₂ ∪
  twoFlipCompletionWords C v c₁ c₃ ∪
  twoFlipCompletionWords C v c₂ c₃

theorem source_allActiveBlock_subset_sevenCubeUnion
    {V : Type*} [LinearOrder V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    {v : V} {c₁ c₂ c₃ : Fin n}
    (hactive :
      retainedActive C v = {c₁,c₂,c₃}) :
    allActiveLossCandidateBlock C v ⊆
      sevenCubeUnion C v c₁ c₂ c₃ := by
  intro word hword
  unfold allActiveLossCandidateBlock at hword
  rcases Finset.mem_union.mp hword with hQ | hT
  · unfold sevenCubeUnion
    simp [hQ]
  · unfold allActiveTranslatedWords at hT
    obtain ⟨d,hdActive,hdWord⟩ :=
      Finset.mem_biUnion.mp hT
    rw [hactive] at hdActive
    simp only [Finset.mem_insert, Finset.mem_singleton] at hdActive
    rcases hdActive with rfl | rfl | rfl
    · unfold sevenCubeUnion
      simp [hdWord]
    · unfold sevenCubeUnion
      simp [hdWord]
    · unfold sevenCubeUnion
      simp [hdWord]

theorem partner_allActiveBlock_subset_sevenCubeUnion_first
    {V : Type*} [LinearOrder V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    {v s₁ : V} {c₁ c₂ c₃ : Fin n}
    (hc12 : c₁ ≠ c₂)
    (hc13 : c₁ ≠ c₃)
    (hactive :
      retainedActive C v = {c₁,c₂,c₃})
    (hwhole :
      WholeCubeQTPair C s₁ v c₁) :
    allActiveLossCandidateBlock C s₁ ⊆
      sevenCubeUnion C v c₁ c₂ c₃ := by
  have hc1V : c₁ ∈ retainedActive C v := by
    rw [hactive]
    simp
  have hc2V : c₂ ∈ retainedActive C v := by
    rw [hactive]
    simp
  have hc3V : c₃ ∈ retainedActive C v := by
    rw [hactive]
    simp
  have hactiveS :
      retainedActive C s₁ = {c₁,c₂,c₃} := by
    rcases hwhole with ⟨hEq,_⟩
    rw [← hEq]
    exact hactive
  have hQeq :
      retainedCompletionWords C s₁ =
        translatedCompletionWords C v c₁ :=
    hwhole.2.symm
  have hTc1 :
      translatedCompletionWords C s₁ c₁ =
        retainedCompletionWords C v :=
    (wholeCubeQTPair_completion_swap_of_active
      C hc1V hwhole).2
  have hTc2 :
      translatedCompletionWords C s₁ c₂ =
        twoFlipCompletionWords C v c₁ c₂ :=
    wholeCubeQTPair_partner_translated_eq_twoFlip
      C hc1V hc2V hc12 hwhole
  have hTc3 :
      translatedCompletionWords C s₁ c₃ =
        twoFlipCompletionWords C v c₁ c₃ :=
    wholeCubeQTPair_partner_translated_eq_twoFlip
      C hc1V hc3V hc13 hwhole
  intro word hword
  unfold allActiveLossCandidateBlock at hword
  rcases Finset.mem_union.mp hword with hQ | hT
  · rw [hQeq] at hQ
    unfold sevenCubeUnion
    simp [hQ]
  · unfold allActiveTranslatedWords at hT
    obtain ⟨d,hdActive,hdWord⟩ :=
      Finset.mem_biUnion.mp hT
    rw [hactiveS] at hdActive
    simp only [Finset.mem_insert, Finset.mem_singleton] at hdActive
    rcases hdActive with rfl | rfl | rfl
    · rw [hTc1] at hdWord
      unfold sevenCubeUnion
      simp [hdWord]
    · rw [hTc2] at hdWord
      unfold sevenCubeUnion
      simp [hdWord]
    · rw [hTc3] at hdWord
      unfold sevenCubeUnion
      simp [hdWord]

theorem partner_allActiveBlock_subset_sevenCubeUnion_second
    {V : Type*} [LinearOrder V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    {v s₂ : V} {c₁ c₂ c₃ : Fin n}
    (hc12 : c₁ ≠ c₂)
    (hc23 : c₂ ≠ c₃)
    (hactive :
      retainedActive C v = {c₁,c₂,c₃})
    (hwhole :
      WholeCubeQTPair C s₂ v c₂) :
    allActiveLossCandidateBlock C s₂ ⊆
      sevenCubeUnion C v c₁ c₂ c₃ := by
  have hc1V : c₁ ∈ retainedActive C v := by
    rw [hactive]
    simp
  have hc2V : c₂ ∈ retainedActive C v := by
    rw [hactive]
    simp
  have hc3V : c₃ ∈ retainedActive C v := by
    rw [hactive]
    simp
  have hactiveS :
      retainedActive C s₂ = {c₁,c₂,c₃} := by
    rcases hwhole with ⟨hEq,_⟩
    rw [← hEq]
    exact hactive
  have hQeq :
      retainedCompletionWords C s₂ =
        translatedCompletionWords C v c₂ :=
    hwhole.2.symm
  have hTc2 :
      translatedCompletionWords C s₂ c₂ =
        retainedCompletionWords C v :=
    (wholeCubeQTPair_completion_swap_of_active
      C hc2V hwhole).2
  have hTc1raw :
      translatedCompletionWords C s₂ c₁ =
        twoFlipCompletionWords C v c₂ c₁ :=
    wholeCubeQTPair_partner_translated_eq_twoFlip
      C hc2V hc1V hc12.symm hwhole
  have hTc1 :
      translatedCompletionWords C s₂ c₁ =
        twoFlipCompletionWords C v c₁ c₂ := by
    rw [hTc1raw,
      twoFlipCompletionWords_comm C v hc12.symm]
  have hTc3 :
      translatedCompletionWords C s₂ c₃ =
        twoFlipCompletionWords C v c₂ c₃ :=
    wholeCubeQTPair_partner_translated_eq_twoFlip
      C hc2V hc3V hc23 hwhole
  intro word hword
  unfold allActiveLossCandidateBlock at hword
  rcases Finset.mem_union.mp hword with hQ | hT
  · rw [hQeq] at hQ
    unfold sevenCubeUnion
    simp [hQ]
  · unfold allActiveTranslatedWords at hT
    obtain ⟨d,hdActive,hdWord⟩ :=
      Finset.mem_biUnion.mp hT
    rw [hactiveS] at hdActive
    simp only [Finset.mem_insert, Finset.mem_singleton] at hdActive
    rcases hdActive with rfl | rfl | rfl
    · rw [hTc1] at hdWord
      unfold sevenCubeUnion
      simp [hdWord]
    · rw [hTc2] at hdWord
      unfold sevenCubeUnion
      simp [hdWord]
    · rw [hTc3] at hdWord
      unfold sevenCubeUnion
      simp [hdWord]

theorem partner_allActiveBlock_subset_sevenCubeUnion_third
    {V : Type*} [LinearOrder V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    {v s₃ : V} {c₁ c₂ c₃ : Fin n}
    (hc13 : c₁ ≠ c₃)
    (hc23 : c₂ ≠ c₃)
    (hactive :
      retainedActive C v = {c₁,c₂,c₃})
    (hwhole :
      WholeCubeQTPair C s₃ v c₃) :
    allActiveLossCandidateBlock C s₃ ⊆
      sevenCubeUnion C v c₁ c₂ c₃ := by
  have hc1V : c₁ ∈ retainedActive C v := by
    rw [hactive]
    simp
  have hc2V : c₂ ∈ retainedActive C v := by
    rw [hactive]
    simp
  have hc3V : c₃ ∈ retainedActive C v := by
    rw [hactive]
    simp
  have hactiveS :
      retainedActive C s₃ = {c₁,c₂,c₃} := by
    rcases hwhole with ⟨hEq,_⟩
    rw [← hEq]
    exact hactive
  have hQeq :
      retainedCompletionWords C s₃ =
        translatedCompletionWords C v c₃ :=
    hwhole.2.symm
  have hTc3 :
      translatedCompletionWords C s₃ c₃ =
        retainedCompletionWords C v :=
    (wholeCubeQTPair_completion_swap_of_active
      C hc3V hwhole).2
  have hTc1raw :
      translatedCompletionWords C s₃ c₁ =
        twoFlipCompletionWords C v c₃ c₁ :=
    wholeCubeQTPair_partner_translated_eq_twoFlip
      C hc3V hc1V hc13.symm hwhole
  have hTc1 :
      translatedCompletionWords C s₃ c₁ =
        twoFlipCompletionWords C v c₁ c₃ := by
    rw [hTc1raw,
      twoFlipCompletionWords_comm C v hc13.symm]
  have hTc2raw :
      translatedCompletionWords C s₃ c₂ =
        twoFlipCompletionWords C v c₃ c₂ :=
    wholeCubeQTPair_partner_translated_eq_twoFlip
      C hc3V hc2V hc23.symm hwhole
  have hTc2 :
      translatedCompletionWords C s₃ c₂ =
        twoFlipCompletionWords C v c₂ c₃ := by
    rw [hTc2raw,
      twoFlipCompletionWords_comm C v hc23.symm]
  intro word hword
  unfold allActiveLossCandidateBlock at hword
  rcases Finset.mem_union.mp hword with hQ | hT
  · rw [hQeq] at hQ
    unfold sevenCubeUnion
    simp [hQ]
  · unfold allActiveTranslatedWords at hT
    obtain ⟨d,hdActive,hdWord⟩ :=
      Finset.mem_biUnion.mp hT
    rw [hactiveS] at hdActive
    simp only [Finset.mem_insert, Finset.mem_singleton] at hdActive
    rcases hdActive with rfl | rfl | rfl
    · rw [hTc1] at hdWord
      unfold sevenCubeUnion
      simp [hdWord]
    · rw [hTc2] at hdWord
      unfold sevenCubeUnion
      simp [hdWord]
    · rw [hTc3] at hdWord
      unfold sevenCubeUnion
      simp [hdWord]

theorem sevenCubeUnion_card_le
    {V : Type*} [LinearOrder V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (v : V) (c₁ c₂ c₃ : Fin n) :
    (sevenCubeUnion C v c₁ c₂ c₃).card
      ≤ 7 * (retainedCompletionWords C v).card := by
  unfold sevenCubeUnion
  have h1 :=
    Finset.card_union_le
      (retainedCompletionWords C v)
      (translatedCompletionWords C v c₁)
  have h2 :=
    Finset.card_union_le
      (retainedCompletionWords C v ∪
        translatedCompletionWords C v c₁)
      (translatedCompletionWords C v c₂)
  have h3 :=
    Finset.card_union_le
      ((retainedCompletionWords C v ∪
        translatedCompletionWords C v c₁) ∪
        translatedCompletionWords C v c₂)
      (translatedCompletionWords C v c₃)
  have h4 :=
    Finset.card_union_le
      (((retainedCompletionWords C v ∪
        translatedCompletionWords C v c₁) ∪
        translatedCompletionWords C v c₂) ∪
        translatedCompletionWords C v c₃)
      (twoFlipCompletionWords C v c₁ c₂)
  have h5 :=
    Finset.card_union_le
      ((((retainedCompletionWords C v ∪
        translatedCompletionWords C v c₁) ∪
        translatedCompletionWords C v c₂) ∪
        translatedCompletionWords C v c₃) ∪
        twoFlipCompletionWords C v c₁ c₂)
      (twoFlipCompletionWords C v c₁ c₃)
  have h6 :=
    Finset.card_union_le
      (((((retainedCompletionWords C v ∪
        translatedCompletionWords C v c₁) ∪
        translatedCompletionWords C v c₂) ∪
        translatedCompletionWords C v c₃) ∪
        twoFlipCompletionWords C v c₁ c₂) ∪
        twoFlipCompletionWords C v c₁ c₃)
      (twoFlipCompletionWords C v c₂ c₃)
  rw [translatedCompletionWords_card,
      translatedCompletionWords_card,
      translatedCompletionWords_card,
      twoFlipCompletionWords_card,
      twoFlipCompletionWords_card,
      twoFlipCompletionWords_card] at
      h1 h2 h3 h4 h5 h6
  omega

#print axioms source_allActiveBlock_subset_sevenCubeUnion
#print axioms partner_allActiveBlock_subset_sevenCubeUnion_first
#print axioms partner_allActiveBlock_subset_sevenCubeUnion_second
#print axioms partner_allActiveBlock_subset_sevenCubeUnion_third
#print axioms sevenCubeUnion_card_le

end OrderedEdgeColoring
end JSP000404Research
