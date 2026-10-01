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

end OrderedEdgeColoring
end JSP000404Research
