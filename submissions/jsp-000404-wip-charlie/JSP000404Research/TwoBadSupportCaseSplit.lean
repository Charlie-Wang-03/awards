import JSP000404Research.ConcreteDeficitThree
import JSP000404Research.TwoSupportOneImpossible
import Mathlib.Tactic

/-!
# Support case split for the remaining two-bad-minimum terminal

In the six-point third-layer profile every minimum has exact exponent n-3.
ConcreteDeficitThree therefore forces its positive quotient support to be
exactly 1, 2, or 3.

Two distinct support-one minima cannot coexist with the n-1 top centre for
n>=5, by the global high-transition packing theorem.

Consequently any ordered pair of distinct bad minima lies in one of the
remaining five unordered support types:
  (1,2), (1,3), (2,2), (2,3), (3,3).
-/

namespace JSP000404Research

theorem deficit_three_support_mem_one_two_three
    {V : Type*} {p : V → Plane}
    (hp : Function.Injective p)
    {t delta : ℝ} {n : ℕ}
    (C : CentreProjectiveCycle hp i)
    (hn4 : 4 ≤ n)
    (hdelta0 : 0 ≤ delta)
    (hdelta1 : delta < 1)
    (ht : t = (n : ℝ) + delta)
    (hexp : centreExponent C t = n - 3) :
    positiveSupport (centreQuotient C t) = 1 ∨
    positiveSupport (centreQuotient C t) = 2 ∨
    positiveSupport (centreQuotient C t) = 3 := by
  rcases concrete_deficit_three_structure
      C hn4 hdelta0 hdelta1 ht hexp with h1 | h2 | h3
  · exact Or.inl h1.1
  · exact Or.inr (Or.inl h2.1)
  · exact Or.inr (Or.inr h3.1)

theorem two_bad_minima_support_five_cases
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane}
    (hp : Function.Injective p)
    (hcap : AngleCap p lam)
    {lam t delta : ℝ} {n : ℕ}
    (hn5 : 5 ≤ n)
    (hdelta0 : 0 ≤ delta)
    (hdeltaHalf : delta < (1 : ℝ) / 2)
    (ht : t = (n : ℝ) + delta)
    (hlam : lam = Real.pi / t)
    {top a b : V}
    (hta : top ≠ a)
    (htb : top ≠ b)
    (hab : a ≠ b)
    (Ctop : CentreProjectiveCycle hp top)
    (Ca : CentreProjectiveCycle hp a)
    (Cb : CentreProjectiveCycle hp b)
    (hTop : centreExponent Ctop t = n - 1)
    (hA : centreExponent Ca t = n - 3)
    (hB : centreExponent Cb t = n - 3) :
    let sa := positiveSupport (centreQuotient Ca t)
    let sb := positiveSupport (centreQuotient Cb t)
    (sa = 1 ∧ sb = 2) ∨
    (sa = 2 ∧ sb = 1) ∨
    (sa = 1 ∧ sb = 3) ∨
    (sa = 3 ∧ sb = 1) ∨
    (sa = 2 ∧ sb = 2) ∨
    (sa = 2 ∧ sb = 3) ∨
    (sa = 3 ∧ sb = 2) ∨
    (sa = 3 ∧ sb = 3) := by
  dsimp only
  have hdelta1 : delta < 1 := by linarith
  have hsa :=
    deficit_three_support_mem_one_two_three
      hp Ca (by omega) hdelta0 hdelta1 ht hA
  have hsb :=
    deficit_three_support_mem_one_two_three
      hp Cb (by omega) hdelta0 hdelta1 ht hB
  rcases hsa with hsa1 | hsa2 | hsa3 <;>
    rcases hsb with hsb1 | hsb2 | hsb3
  · exfalso
    exact no_top_two_deficit_three_support_one
      hp hcap hn5 hdelta0 hdeltaHalf ht hlam
      hta htb hab Ctop Ca Cb hTop hA hB hsa1 hsb1
  · exact Or.inl ⟨hsa1, hsb2⟩
  · exact Or.inr (Or.inr (Or.inl ⟨hsa1, hsb3⟩))
  · exact Or.inr (Or.inl ⟨hsa2, hsb1⟩)
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨hsa2, hsb2⟩))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr
      (Or.inr (Or.inl ⟨hsa2, hsb3⟩)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨hsa3, hsb1⟩)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr
      (Or.inr (Or.inr (Or.inl ⟨hsa3, hsb2⟩))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr
      (Or.inr (Or.inr (Or.inr ⟨hsa3, hsb3⟩))))))

#print axioms deficit_three_support_mem_one_two_three
#print axioms two_bad_minima_support_five_cases

end JSP000404Research
