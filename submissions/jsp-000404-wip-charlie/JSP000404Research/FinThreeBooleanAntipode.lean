import JSP000404Research.ResidualPairLocalFlip
import Mathlib.Tactic

/-!
# Three-coordinate Boolean flip algebra

Elementary normalization lemmas for the n=3 Q/T/T/T terminal.
-/

namespace JSP000404Research
namespace OrderedEdgeColoring

theorem flipBoolWordAt_comm
    {n : ℕ}
    (word : Fin n → Bool)
    {c d : Fin n}
    (hcd : c ≠ d) :
    flipBoolWordAt (flipBoolWordAt word c) d =
      flipBoolWordAt (flipBoolWordAt word d) c := by
  funext q
  by_cases hqc : q = c
  · subst q
    rw [flipBoolWordAt_at]
    rw [flipBoolWordAt_off _ hcd]
    rw [flipBoolWordAt_off _ hcd.symm]
    rw [flipBoolWordAt_at]
  · by_cases hqd : q = d
    · subst q
      rw [flipBoolWordAt_at]
      rw [flipBoolWordAt_off _ hcd.symm]
      rw [flipBoolWordAt_at]
      rw [flipBoolWordAt_off _ hcd]
    · simp [flipBoolWordAt, hqc, hqd]

theorem three_distinct_fin3_exhaust
    {a b c q : Fin 3}
    (hab : a ≠ b)
    (hac : a ≠ c)
    (hbc : b ≠ c) :
    q = a ∨ q = b ∨ q = c := by
  have ha : a.val < 3 := a.isLt
  have hb : b.val < 3 := b.isLt
  have hc : c.val < 3 := c.isLt
  have hq : q.val < 3 := q.isLt
  have habv : a.val ≠ b.val := by
    intro h
    exact hab (Fin.ext h)
  have hacv : a.val ≠ c.val := by
    intro h
    exact hac (Fin.ext h)
  have hbcv : b.val ≠ c.val := by
    intro h
    exact hbc (Fin.ext h)
  have hcase :
      q.val = a.val ∨ q.val = b.val ∨ q.val = c.val := by
    omega
  rcases hcase with h | h | h
  · exact Or.inl (Fin.ext h)
  · exact Or.inr (Or.inl (Fin.ext h))
  · exact Or.inr (Or.inr (Fin.ext h))

noncomputable def tripleFlipBoolWord
    (word : Fin 3 → Bool)
    (a b c : Fin 3) :
    Fin 3 → Bool :=
  flipBoolWordAt
    (flipBoolWordAt
      (flipBoolWordAt word a) b) c

theorem tripleFlipBoolWord_at
    (word : Fin 3 → Bool)
    {a b c q : Fin 3}
    (hab : a ≠ b)
    (hac : a ≠ c)
    (hbc : b ≠ c) :
    tripleFlipBoolWord word a b c q = !(word q) := by
  rcases three_distinct_fin3_exhaust hab hac hbc (q := q)
    with rfl | rfl | rfl
  · unfold tripleFlipBoolWord
    rw [flipBoolWordAt_off _ hac.symm]
    rw [flipBoolWordAt_off _ hab.symm]
    rw [flipBoolWordAt_at]
  · unfold tripleFlipBoolWord
    rw [flipBoolWordAt_off _ hbc.symm]
    rw [flipBoolWordAt_at]
    rw [flipBoolWordAt_off _ hab]
  · unfold tripleFlipBoolWord
    rw [flipBoolWordAt_at]
    rw [flipBoolWordAt_off _ hbc]
    rw [flipBoolWordAt_off _ hac]

theorem tripleFlipBoolWord_eq_not
    (word : Fin 3 → Bool)
    {a b c : Fin 3}
    (hab : a ≠ b)
    (hac : a ≠ c)
    (hbc : b ≠ c) :
    tripleFlipBoolWord word a b c =
      fun q => !(word q) := by
  funext q
  exact tripleFlipBoolWord_at word hab hac hbc

theorem tripleFlipBoolWord_ne_word
    (word : Fin 3 → Bool)
    {a b c : Fin 3}
    (hab : a ≠ b)
    (hac : a ≠ c)
    (hbc : b ≠ c) :
    tripleFlipBoolWord word a b c ≠ word := by
  intro h
  have ha :=
    congrFun h a
  rw [tripleFlipBoolWord_at word hab hac hbc] at ha
  cases hw : word a <;> simp [hw] at ha

/-- The antipode differs from each one-coordinate neighbour. -/
theorem tripleFlipBoolWord_ne_singleFlip
    (word : Fin 3 → Bool)
    {a b c d : Fin 3}
    (hab : a ≠ b)
    (hac : a ≠ c)
    (hbc : b ≠ c) :
    tripleFlipBoolWord word a b c ≠
      flipBoolWordAt word d := by
  intro h
  obtain hd : d = a ∨ d = b ∨ d = c :=
    three_distinct_fin3_exhaust hab hac hbc (q := d)
  -- choose one of the other two coordinates; the single flip leaves it
  -- unchanged whereas the antipode flips it.
  rcases hd with rfl | rfl | rfl
  · have hbEq := congrFun h b
    rw [tripleFlipBoolWord_at word hab hac hbc] at hbEq
    rw [flipBoolWordAt_off word hab.symm] at hbEq
    cases hw : word b <;> simp [hw] at hbEq
  · have haEq := congrFun h a
    rw [tripleFlipBoolWord_at word hab hac hbc] at haEq
    rw [flipBoolWordAt_off word hab] at haEq
    cases hw : word a <;> simp [hw] at haEq
  · have haEq := congrFun h a
    rw [tripleFlipBoolWord_at word hab hac hbc] at haEq
    rw [flipBoolWordAt_off word hac] at haEq
    cases hw : word a <;> simp [hw] at haEq

#print axioms flipBoolWordAt_comm
#print axioms three_distinct_fin3_exhaust
#print axioms tripleFlipBoolWord_eq_not
#print axioms tripleFlipBoolWord_ne_singleFlip


theorem twoFlipBoolWord_ne_tripleFlip
    (word : Fin 3 → Bool)
    {a b c : Fin 3}
    (hab : a ≠ b)
    (hac : a ≠ c)
    (hbc : b ≠ c) :
    flipBoolWordAt (flipBoolWordAt word a) b ≠
      tripleFlipBoolWord word a b c := by
  intro h
  have hcEq := congrFun h c
  rw [flipBoolWordAt_off _ hbc.symm] at hcEq
  rw [flipBoolWordAt_off word hac.symm] at hcEq
  rw [tripleFlipBoolWord_at word hab hac hbc] at hcEq
  cases hw : word c <;> simp [hw] at hcEq

theorem tripleFlipBoolWord_ne_doubleFlip
    (word : Fin 3 → Bool)
    {a b c : Fin 3}
    (hab : a ≠ b)
    (hac : a ≠ c)
    (hbc : b ≠ c) :
    tripleFlipBoolWord word a b c ≠
      flipBoolWordAt (flipBoolWordAt word a) b :=
  (twoFlipBoolWord_ne_tripleFlip word hab hac hbc).symm

/-- From any one-coordinate neighbour of a Fin-3 word, a further single flip
still cannot reach the antipode unless it is followed by both remaining
coordinates.  In particular one extra flip from a one-flip base never reaches
the triple antipode. -/
theorem tripleFlipBoolWord_ne_flip_singleFlip
    (word : Fin 3 → Bool)
    {a b c d : Fin 3}
    (hab : a ≠ b)
    (hac : a ≠ c)
    (hbc : b ≠ c) :
    tripleFlipBoolWord word a b c ≠
      flipBoolWordAt (flipBoolWordAt word a) d := by
  obtain hd : d = a ∨ d = b ∨ d = c :=
    three_distinct_fin3_exhaust hab hac hbc (q := d)
  rcases hd with rfl | rfl | rfl
  · rw [flipBoolWordAt_involutive]
    exact tripleFlipBoolWord_ne_word word hab hac hbc
  · exact tripleFlipBoolWord_ne_doubleFlip word hab hac hbc
  · intro h
    have hbEq := congrFun h b
    rw [tripleFlipBoolWord_at word hab hac hbc] at hbEq
    rw [flipBoolWordAt_off _ hbc.symm] at hbEq
    rw [flipBoolWordAt_off word hab.symm] at hbEq
    cases hw : word b <;> simp [hw] at hbEq

#print axioms tripleFlipBoolWord_ne_doubleFlip
#print axioms tripleFlipBoolWord_ne_flip_singleFlip


theorem tripleFlipBoolWord_eq_twoFlip_from_firstNeighbour
    (word : Fin 3 → Bool)
    (a b c : Fin 3) :
    tripleFlipBoolWord word a b c =
      flipBoolWordAt
        (flipBoolWordAt (flipBoolWordAt word a) b) c := rfl

theorem tripleFlipBoolWord_eq_twoFlip_from_secondNeighbour
    (word : Fin 3 → Bool)
    {a b c : Fin 3}
    (hab : a ≠ b)
    (hac : a ≠ c)
    (hbc : b ≠ c) :
    tripleFlipBoolWord word a b c =
      flipBoolWordAt
        (flipBoolWordAt (flipBoolWordAt word b) a) c := by
  unfold tripleFlipBoolWord
  rw [flipBoolWordAt_comm word hab]

theorem tripleFlipBoolWord_eq_twoFlip_from_thirdNeighbour
    (word : Fin 3 → Bool)
    {a b c : Fin 3}
    (hab : a ≠ b)
    (hac : a ≠ c)
    (hbc : b ≠ c) :
    tripleFlipBoolWord word a b c =
      flipBoolWordAt
        (flipBoolWordAt (flipBoolWordAt word c) a) b := by
  funext q
  rw [tripleFlipBoolWord_at word hab hac hbc]
  obtain hq : q = a ∨ q = b ∨ q = c :=
    three_distinct_fin3_exhaust hab hac hbc (q := q)
  rcases hq with rfl | rfl | rfl
  · rw [flipBoolWordAt_off _ hab.symm]
    rw [flipBoolWordAt_at]
    rw [flipBoolWordAt_off word hac]
  · rw [flipBoolWordAt_at]
    rw [flipBoolWordAt_off _ hab]
    rw [flipBoolWordAt_off word hbc]
  · rw [flipBoolWordAt_off _ hbc]
    rw [flipBoolWordAt_off _ hac]
    rw [flipBoolWordAt_at]

#print axioms tripleFlipBoolWord_eq_twoFlip_from_secondNeighbour
#print axioms tripleFlipBoolWord_eq_twoFlip_from_thirdNeighbour


/-- Every Fin-3 Boolean word is either the base word, a one-coordinate
neighbour of it, the antipode, or a one-coordinate neighbour of the antipode.
Equivalently the two radius-one Hamming balls around antipodal vertices cover
the whole 3-cube. -/
theorem fin3_word_base_or_single_or_antipode_or_antipode_single
    (base q : Fin 3 → Bool)
    {a b c : Fin 3}
    (hab : a ≠ b)
    (hac : a ≠ c)
    (hbc : b ≠ c) :
    q = base
    ∨ (∃ d : Fin 3, q = flipBoolWordAt base d)
    ∨ q = tripleFlipBoolWord base a b c
    ∨ (∃ d : Fin 3,
        q = flipBoolWordAt
          (tripleFlipBoolWord base a b c) d) := by
  classical
  let S : Finset (Fin 3) :=
    Finset.univ.filter fun d => q d ≠ base d
  have hcard : S.card ≤ 3 := by
    simpa using Finset.card_le_univ S
  interval_cases h : S.card
  · left
    funext d
    have hdNot : d ∉ S := by
      intro hd
      have hp := Finset.card_pos.mpr ⟨d,hd⟩
      omega
    simpa [S] using hdNot
  · right; left
    obtain ⟨d,hdS,hS⟩ := Finset.card_eq_one.mp h
    refine ⟨d,?_⟩
    funext e
    by_cases hed : e = d
    · subst e
      have hdiff : q d ≠ base d := by
        have : d ∈ S := by rw [hS]; simp
        simpa [S] using this
      cases hq : q d <;> cases hb : base d <;>
        simp [hq,hb] at hdiff ⊢
    · have heNot : e ∉ S := by
        rw [hS]
        simp [hed]
      have heEq : q e = base e := by
        simpa [S] using heNot
      rw [flipBoolWordAt_off base hed]
      exact heEq
  · right; right; right
    -- With exactly two differing coordinates, there is a unique coordinate
    -- on which q agrees with base.  Flipping that coordinate in the antipode
    -- gives q.
    have hcomp :
        ((Finset.univ : Finset (Fin 3))  S).card = 1 := by
      rw [Finset.card_sdiff]
      · simp [h]
      · exact Finset.filter_subset _ _
    obtain ⟨d,hdEq⟩ := Finset.card_eq_one.mp hcomp
    refine ⟨d,?_⟩
    funext e
    have hanti :=
      tripleFlipBoolWord_at base hab hac hbc (q := e)
    by_cases hed : e = d
    · subst e
      have hdComp : d ∈ (Finset.univ : Finset (Fin 3))  S := by
        rw [hdEq]
        simp
      have hdNotS := (Finset.mem_sdiff.mp hdComp).2
      have hdBase : q d = base d := by
        simpa [S] using hdNotS
      rw [flipBoolWordAt_at, hanti, hdBase]
      cases hb : base d <;> simp [hb]
    · have heNotComp :
          e ∉ (Finset.univ : Finset (Fin 3))  S := by
        rw [hdEq]
        simp [hed]
      have heS : e ∈ S := by
        by_contra heNotS
        apply heNotComp
        exact Finset.mem_sdiff.mpr ⟨by simp,heNotS⟩
      have heDiff : q e ≠ base e := by
        simpa [S] using heS
      rw [flipBoolWordAt_off _ hed, hanti]
      cases hq : q e <;> cases hb : base e <;>
        simp [hq,hb] at heDiff ⊢
  · right; right; left
    funext d
    rw [tripleFlipBoolWord_at base hab hac hbc]
    have hdS : d ∈ S := by
      by_contra hdNot
      have hsub :
          S ⊆ (Finset.univ : Finset (Fin 3)).erase d := by
        intro e he
        exact Finset.mem_erase.mpr
          ⟨by
            intro hed
            subst e
            exact hdNot he,
           by simp⟩
      have hc := Finset.card_le_card hsub
      simp [h] at hc
    have hdiff : q d ≠ base d := by
      simpa [S] using hdS
    cases hq : q d <;> cases hb : base d <;>
      simp [hq,hb] at hdiff ⊢

#print axioms fin3_word_base_or_single_or_antipode_or_antipode_single

end OrderedEdgeColoring
end JSP000404Research
