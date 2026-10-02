import JSP000404Research.ResidualQTTTWholeCubeCoreSplit
import JSP000404Research.ResidualLossAllActiveCandidateBlock
import JSP000404Research.FinThreeBooleanAntipode
import Mathlib.Tactic

/-!
# Three-coordinate antipode exclusion in arbitrary ambient dimension

The n=3 Q/T/T/T deficiency argument uses the Boolean antipode of the common
word.  The same local exclusion does not require n=3: whenever a projected-loss
vertex has retained-active palette exactly {a,b,c}, the word obtained by
flipping all three coordinates cannot belong to its enlarged candidate block.

Indeed Q_v fixes all three coordinates.  The triple flip violates all three,
while one translated slice can repair at most one of them.

For an equal-palette Q/T partner, its completion base is one single flip of the
common Q-word.  Relative to that base, the same triple antipode is a two-flip
word, so it is again outside the enlarged block.
-/

namespace JSP000404Research
namespace OrderedEdgeColoring

noncomputable def tripleFlipBoolWordN
    {n : ℕ}
    (word : Fin n → Bool)
    (a b c : Fin n) :
    Fin n → Bool :=
  flipBoolWordAt
    (flipBoolWordAt
      (flipBoolWordAt word a) b) c

theorem tripleFlipBoolWordN_at_a
    {n : ℕ}
    (word : Fin n → Bool)
    {a b c : Fin n}
    (hab : a ≠ b) (hac : a ≠ c) :
    tripleFlipBoolWordN word a b c a = !(word a) := by
  unfold tripleFlipBoolWordN
  rw [flipBoolWordAt_off _ hac.symm,
      flipBoolWordAt_off _ hab.symm,
      flipBoolWordAt_at]

theorem tripleFlipBoolWordN_at_b
    {n : ℕ}
    (word : Fin n → Bool)
    {a b c : Fin n}
    (hab : a ≠ b) (hbc : b ≠ c) :
    tripleFlipBoolWordN word a b c b = !(word b) := by
  unfold tripleFlipBoolWordN
  rw [flipBoolWordAt_off _ hbc.symm,
      flipBoolWordAt_at,
      flipBoolWordAt_off _ hab]

theorem tripleFlipBoolWordN_at_c
    {n : ℕ}
    (word : Fin n → Bool)
    {a b c : Fin n}
    (hac : a ≠ c) (hbc : b ≠ c) :
    tripleFlipBoolWordN word a b c c = !(word c) := by
  unfold tripleFlipBoolWordN
  rw [flipBoolWordAt_at,
      flipBoolWordAt_off _ hbc,
      flipBoolWordAt_off _ hac]

theorem tripleFlipBoolWordN_not_mem_completion_of_three_active
    {V : Type*} [LinearOrder V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    {v : V} {word : Fin n → Bool}
    {a b c : Fin n}
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (ha : a ∈ retainedActive C v)
    (hb : b ∈ retainedActive C v)
    (hc : c ∈ retainedActive C v)
    (hword : word ∈ retainedCompletionWords C v) :
    tripleFlipBoolWordN word a b c ∉
      retainedCompletionWords C v := by
  intro hanti
  have hbase :=
    (mem_retainedCompletionWords C v word).1 hword
  have hfix :=
    (mem_retainedCompletionWords C v
      (tripleFlipBoolWordN word a b c)).1 hanti
  have hbaseA := hbase a ha
  have hantiA := hfix a ha
  rw [tripleFlipBoolWordN_at_a word hab hac, hbaseA] at hantiA
  cases h : retainedBit C v a <;> simp [h] at hantiA

theorem tripleFlipBoolWordN_not_mem_translated_of_three_active
    {V : Type*} [LinearOrder V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    {v : V} {word : Fin n → Bool}
    {a b c d : Fin n}
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (ha : a ∈ retainedActive C v)
    (hb : b ∈ retainedActive C v)
    (hc : c ∈ retainedActive C v)
    (hword : word ∈ retainedCompletionWords C v) :
    tripleFlipBoolWordN word a b c ∉
      translatedCompletionWords C v d := by
  intro hantiT
  have hantiBase :
      flipBoolWordAt (tripleFlipBoolWordN word a b c) d ∈
        retainedCompletionWords C v :=
    (mem_translatedCompletionWords
      C v d (tripleFlipBoolWordN word a b c)).1 hantiT
  have hbase :=
    (mem_retainedCompletionWords C v word).1 hword
  have hcomp :=
    (mem_retainedCompletionWords C v
      (flipBoolWordAt (tripleFlipBoolWordN word a b c) d)).1
      hantiBase
  by_cases hda : d = a
  · subst d
    have h1 := hbase b hb
    have h2 := hcomp b hb
    rw [flipBoolWordAt_off _ hab.symm,
        tripleFlipBoolWordN_at_b word hab hbc,
        h1] at h2
    cases h : retainedBit C v b <;> simp [h] at h2
  · have h1 := hbase a ha
    have h2 := hcomp a ha
    rw [flipBoolWordAt_off _ hda,
        tripleFlipBoolWordN_at_a word hab hac,
        h1] at h2
    cases h : retainedBit C v a <;> simp [h] at h2

theorem tripleFlipBoolWordN_outside_enlarged_of_three_active
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    {v : V} {word : Fin n → Bool}
    {a b c : Fin n}
    (hvLoss : v ∈ projectedLossVertices C exponent)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (ha : a ∈ retainedActive C v)
    (hb : b ∈ retainedActive C v)
    (hc : c ∈ retainedActive C v)
    (hword : word ∈ retainedCompletionWords C v) :
    tripleFlipBoolWordN word a b c ∉
      enlargedProjectedCandidateBlock C exponent v := by
  classical
  rw [enlargedProjectedCandidateBlock_loss C exponent hvLoss]
  unfold allActiveLossCandidateBlock
  intro hmem
  rcases Finset.mem_union.mp hmem with hQ | hT
  · exact tripleFlipBoolWordN_not_mem_completion_of_three_active
      C hab hac hbc ha hb hc hword hQ
  · unfold allActiveTranslatedWords at hT
    obtain ⟨d,hd,hTd⟩ := Finset.mem_biUnion.mp hT
    exact tripleFlipBoolWordN_not_mem_translated_of_three_active
      C hab hac hbc ha hb hc hword hTd

theorem tripleFlipBoolWordN_outside_enlarged_of_exact_three_palette
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    {v : V} {word : Fin n → Bool}
    {a b c : Fin n}
    (hvLoss : v ∈ projectedLossVertices C exponent)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hactive : retainedActive C v = {a,b,c})
    (hword : word ∈ retainedCompletionWords C v) :
    tripleFlipBoolWordN word a b c ∉
      enlargedProjectedCandidateBlock C exponent v := by
  apply tripleFlipBoolWordN_outside_enlarged_of_three_active
    C exponent hvLoss hab hac hbc
  · rw [hactive]; simp
  · rw [hactive]; simp
  · rw [hactive]; simp
  · exact hword

/-- Equal-palette Q/T partner form.  The common Q-word is translated at v
along owner coordinate a, and v has the same three-coordinate palette as s.
The triple owner-coordinate antipode is outside v's enlarged block. -/
theorem QTT_equal_palette_partner_excludes_triple_antipode
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    {s v : V} {word : Fin n → Bool}
    {a b c : Fin n}
    (hvLoss : v ∈ projectedLossVertices C exponent)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hsActive : retainedActive C s = {a,b,c})
    (hactiveEq : retainedActive C v = retainedActive C s)
    (haV : a ∈ retainedActive C v)
    (hvT : word ∈ translatedCompletionWords C v a) :
    tripleFlipBoolWordN word a b c ∉
      enlargedProjectedCandidateBlock C exponent v := by
  have hvActive : retainedActive C v = {a,b,c} := by
    rw [hactiveEq, hsActive]
  have hbase :
      flipBoolWordAt word a ∈ retainedCompletionWords C v :=
    (mem_translatedCompletionWords C v a word).1 hvT

  -- Relative to the completion base flip_a(word), the target differs at b,c.
  rw [enlargedProjectedCandidateBlock_loss C exponent hvLoss]
  unfold allActiveLossCandidateBlock
  intro hmem
  rcases Finset.mem_union.mp hmem with hQ | hT
  · have hcomp :=
      (mem_retainedCompletionWords C v
        (tripleFlipBoolWordN word a b c)).1 hQ
    have hbaseC :=
      (mem_retainedCompletionWords C v
        (flipBoolWordAt word a)).1 hbase
    have hbV : b ∈ retainedActive C v := by rw [hvActive]; simp
    have h1 := hbaseC b hbV
    have h2 := hcomp b hbV
    rw [flipBoolWordAt_off word hab,
        tripleFlipBoolWordN_at_b word hab hbc, h1] at h2
    cases h : retainedBit C v b <;> simp [h] at h2
  · unfold allActiveTranslatedWords at hT
    obtain ⟨d,hd,hTd⟩ := Finset.mem_biUnion.mp hT
    have hdCase : d = a ∨ d = b ∨ d = c := by
      rw [hvActive] at hd
      simpa using hd
    have hantiBase :
        flipBoolWordAt (tripleFlipBoolWordN word a b c) d ∈
          retainedCompletionWords C v :=
      (mem_translatedCompletionWords
        C v d (tripleFlipBoolWordN word a b c)).1 hTd
    have hcomp :=
      (mem_retainedCompletionWords C v
        (flipBoolWordAt (tripleFlipBoolWordN word a b c) d)).1
        hantiBase
    have hbaseComp :=
      (mem_retainedCompletionWords C v
        (flipBoolWordAt word a)).1 hbase
    have hbV : b ∈ retainedActive C v := by rw [hvActive]; simp
    have hcV : c ∈ retainedActive C v := by rw [hvActive]; simp
    rcases hdCase with rfl | rfl | rfl
    · have h1 := hbaseComp b hbV
      have h2 := hcomp b hbV
      rw [flipBoolWordAt_off _ hab.symm,
          tripleFlipBoolWordN_at_b word hab hbc] at h2
      rw [flipBoolWordAt_off word hab] at h1
      rw [h1] at h2
      cases h : retainedBit C v b <;> simp [h] at h2
    · have h1 := hbaseComp c hcV
      have h2 := hcomp c hcV
      rw [flipBoolWordAt_off _ hbc,
          tripleFlipBoolWordN_at_c word hac hbc] at h2
      rw [flipBoolWordAt_off word hac] at h1
      rw [h1] at h2
      cases h : retainedBit C v c <;> simp [h] at h2
    · have h1 := hbaseComp b hbV
      have h2 := hcomp b hbV
      rw [flipBoolWordAt_off _ hbc.symm,
          tripleFlipBoolWordN_at_b word hab hbc] at h2
      rw [flipBoolWordAt_off word hab] at h1
      rw [h1] at h2
      cases h : retainedBit C v b <;> simp [h] at h2

#print axioms tripleFlipBoolWordN_outside_enlarged_of_exact_three_palette
#print axioms QTT_equal_palette_partner_excludes_triple_antipode

end OrderedEdgeColoring
end JSP000404Research
