import JSP000404Research.FourCentreSupportTwoContradiction
import Mathlib.Tactic

/-!
# Pair classification among the three non-centre vertices of Fin 4

Fix four pairwise-distinct vertices s,a,b,c and view b as the centre.  Any two
distinct elements of OtherVertex b form exactly one of the unordered pairs

  {s,a}, {s,c}, {a,c}.

This tiny finite lemma keeps later mixed-branch proofs free of repeated Fin 4
case explosions.
-/

namespace JSP000404Research

theorem other_pair_at_b_three_cases_fin_four
    {s a b c : Fin 4}
    (hsa : s ≠ a) (hsb : s ≠ b) (hsc : s ≠ c)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (x y : OtherVertex b)
    (hxy : x ≠ y) :
    ((x.1 = s ∧ y.1 = a) ∨ (x.1 = a ∧ y.1 = s)) ∨
    ((x.1 = s ∧ y.1 = c) ∨ (x.1 = c ∧ y.1 = s)) ∨
    ((x.1 = a ∧ y.1 = c) ∨ (x.1 = c ∧ y.1 = a)) := by
  have hcover :=
    fin_four_exhaust_of_four_distinct
      hsa hsb hsc hab hac hbc
  have hx :
      x.1 = s ∨ x.1 = a ∨ x.1 = c := by
    rcases hcover x.1 with hs | ha | hb | hc
    · exact Or.inl hs
    · exact Or.inr (Or.inl ha)
    · exact False.elim (x.2 hb)
    · exact Or.inr (Or.inr hc)
  have hy :
      y.1 = s ∨ y.1 = a ∨ y.1 = c := by
    rcases hcover y.1 with hs | ha | hb | hc
    · exact Or.inl hs
    · exact Or.inr (Or.inl ha)
    · exact False.elim (y.2 hb)
    · exact Or.inr (Or.inr hc)
  rcases hx with hs | ha | hc <;>
    rcases hy with hs' | ha' | hc'
  · exfalso
    apply hxy
    apply Subtype.ext
    rw [hs, hs']
  · exact Or.inl (Or.inl ⟨hs, ha'⟩)
  · exact Or.inr (Or.inl (Or.inl ⟨hs, hc'⟩))
  · exact Or.inl (Or.inr ⟨ha, hs'⟩)
  · exfalso
    apply hxy
    apply Subtype.ext
    rw [ha, ha']
  · exact Or.inr (Or.inr (Or.inl ⟨ha, hc'⟩))
  · exact Or.inr (Or.inl (Or.inr ⟨hc, hs'⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨hc, ha'⟩))
  · exfalso
    apply hxy
    apply Subtype.ext
    rw [hc, hc']

#print axioms other_pair_at_b_three_cases_fin_four

end JSP000404Research
