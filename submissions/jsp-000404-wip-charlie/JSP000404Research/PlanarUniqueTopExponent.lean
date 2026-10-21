import JSP000404Research.ConcreteSharpCentre
import Mathlib.Tactic

/-!
# Genuine planar top layer uniqueness under the lower-branch AngleCap

For n >= 3 and delta < 1/2, any actual exponent n-1 centre is
Sendov-sharp (existing certified concrete_unit_deficit_is_sharp).
Two distinct sharp centres cannot coexist with any third centre
under genuine AngleCap (existing two_sharp_no_third_small_delta).

The lemma below gives the precise all-cardinality witness-free
top-exponent multiplicity obstruction, with no six-source debt-payment
assumption and no extra sharpness premise.
-/

namespace JSP000404Research

theorem no_two_top_exponents_with_third
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane}
    (hp : Function.Injective p)
    {lam t delta : ℝ} {n : ℕ}
    (hcap : AngleCap p lam)
    (hn : 3 ≤ n)
    (hdelta0 : 0 ≤ delta)
    (hdeltaHalf : delta < (1 : ℝ) / 2)
    (ht : t = (n : ℝ) + delta)
    (hlam : lam = Real.pi / t)
    (C : ∀ i : V, CentreProjectiveCycle hp i)
    {s a b : V}
    (hsa : s ≠ a) (hsb : s ≠ b) (hab : a ≠ b)
    (hs : centreExponent (C s) t = n - 1)
    (ha : centreExponent (C a) t = n - 1) :
    False := by
  have hdelta1 : delta < 1 := by linarith
  have hn2 : 2 ≤ n := by omega
  have hnReal : (3 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have htpos : 0 < t := by rw [ht]; linarith
  have hlampos : 0 < lam := by
    rw [hlam]
    exact div_pos Real.pi_pos htpos
  have hsharpS : SharpAt p delta lam s :=
    concrete_unit_deficit_is_sharp
      hp hcap hn2 hdelta0 hdelta1 ht hlam s (C s) hs
  have hsharpA : SharpAt p delta lam a :=
    concrete_unit_deficit_is_sharp
      hp hcap hn2 hdelta0 hdelta1 ht hlam a (C a) ha
  exact two_sharp_no_third_small_delta
    hp hcap hdeltaHalf hlampos hsa hsb hab hsharpS hsharpA

/-- If the finite configuration has at least three vertices, no two
distinct true original centres can both occupy the exponent n-1 layer. -/
theorem top_exponent_unique_of_card_ge_three
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane}
    (hp : Function.Injective p)
    {lam t delta : ℝ} {n : ℕ}
    (hcap : AngleCap p lam)
    (hn : 3 ≤ n)
    (hcard : 3 ≤ Fintype.card V)
    (hdelta0 : 0 ≤ delta)
    (hdeltaHalf : delta < (1 : ℝ) / 2)
    (ht : t = (n : ℝ) + delta)
    (hlam : lam = Real.pi / t)
    (C : ∀ i : V, CentreProjectiveCycle hp i)
    (s a : V)
    (hsa : s ≠ a)
    (hs : centreExponent (C s) t = n - 1)
    (ha : centreExponent (C a) t = n - 1) :
    False := by
  classical
  have hthird : ∃ b : V, b ≠ s ∧ b ≠ a := by
    by_contra hnot
    have hcovered : ∀ b : V, b = s ∨ b = a := by
      intro b
      by_cases hbs : b = s
      · exact Or.inl hbs
      · have hba : b = a := by
          by_contra hba
          exact hnot ⟨b, hbs, hba⟩
        exact Or.inr hba
    have hsub : (Finset.univ : Finset V) ⊆ ({s, a} : Finset V) := by
      intro b _
      rcases hcovered b with hbs | hba
      · simp [hbs]
      · simp [hba]
    have hc : Fintype.card V ≤ 2 := by
      calc
        Fintype.card V = (Finset.univ : Finset V).card := by simp
        _ ≤ ({s, a} : Finset V).card :=
          Finset.card_le_card hsub
        _ ≤ 2 := by simp
    omega
  obtain ⟨b, hbs, hba⟩ := hthird
  exact no_two_top_exponents_with_third
    hp hcap hn hdelta0 hdeltaHalf ht hlam C
    hsa hbs.symm hba.symm hs ha

#print axioms no_two_top_exponents_with_third
#print axioms top_exponent_unique_of_card_ge_three

end JSP000404Research
