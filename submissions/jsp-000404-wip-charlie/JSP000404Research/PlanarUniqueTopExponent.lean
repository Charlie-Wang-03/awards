import JSP000404Research.ConcreteSharpCentre
import JSP000404Research.NoTopTwoNextMultiplicity
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
        _ ≤ 2 := by simp [hsa, Ne.symm hsa]
    omega
  obtain ⟨b, hbs, hba⟩ := hthird
  exact no_two_top_exponents_with_third
    hp hcap hn hdelta0 hdeltaHalf ht hlam C
    hsa hbs.symm hba.symm hs ha


/-- With a genuine top centre and at least four original centres,
two other distinct next-layer centres are geometrically impossible. The
fourth-centre witness is derived from actual cardinality, not assumed. -/
theorem no_two_next_exponents_beside_top_of_card_ge_four
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane}
    (hp : Function.Injective p)
    {lam t delta : ℝ} {n : ℕ}
    (hcap : AngleCap p lam)
    (hn : 3 ≤ n)
    (hcard : 4 ≤ Fintype.card V)
    (hdelta0 : 0 ≤ delta)
    (hdeltaHalf : delta < (1 : ℝ) / 2)
    (ht : t = (n : ℝ) + delta)
    (hlam : lam = Real.pi / t)
    (C : ∀ i : V, CentreProjectiveCycle hp i)
    {s a b : V}
    (hsa : s ≠ a) (hsb : s ≠ b) (hab : a ≠ b)
    (hs : centreExponent (C s) t = n - 1)
    (ha : centreExponent (C a) t = n - 2)
    (hb : centreExponent (C b) t = n - 2) :
    False := by
  classical
  have hfourth : ∃ c : V, c ≠ s ∧ c ≠ a ∧ c ≠ b := by
    by_contra hnot
    have hcovered : ∀ c : V, c = s ∨ c = a ∨ c = b := by
      intro c
      by_cases hcs : c = s
      · exact Or.inl hcs
      · by_cases hca : c = a
        · exact Or.inr (Or.inl hca)
        · have hcb : c = b := by
            by_contra hcb
            exact hnot ⟨c, hcs, hca, hcb⟩
          exact Or.inr (Or.inr hcb)
    have hsub : (Finset.univ : Finset V) ⊆ ({s, a, b} : Finset V) := by
      intro c _
      rcases hcovered c with hcs | hca | hcb
      · simp [hcs]
      · simp [hca]
      · simp [hcb]
    have hc : Fintype.card V ≤ 3 := by
      calc
        Fintype.card V = (Finset.univ : Finset V).card := by simp
        _ ≤ ({s, a, b} : Finset V).card :=
          Finset.card_le_card hsub
        _ ≤ 3 := by simp [hsa, hsb, hab]
    omega
  obtain ⟨c, hcs, hca, hcb⟩ := hfourth
  exact no_top_and_two_next_with_fourth
    hp hcap hn hdelta0 hdeltaHalf ht hlam
    hsa hsb hcs.symm hab hca.symm hcb.symm
    (C s) (C a) (C b) hs ha hb


/-- Quantitative form of the actual planar unique-top theorem, suitable
for direct use in dyadic layer censuses. -/
theorem actual_top_exponent_layer_card_le_one
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
    (C : ∀ i : V, CentreProjectiveCycle hp i) :
    ((Finset.univ : Finset V).filter
      (fun i => centreExponent (C i) t = n - 1)).card ≤ 1 := by
  classical
  apply Finset.card_le_one.mpr
  intro s hs a ha
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hs ha
  by_contra hne
  exact top_exponent_unique_of_card_ge_three
    hp hcap hn hcard hdelta0 hdeltaHalf ht hlam C
    s a hne hs ha

/-- Given a true top exponent, there is at most one DIFFERENT centre
in the next exponent layer, whenever four actual centres exist. -/
theorem actual_next_exponent_layer_card_le_one_of_top
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane}
    (hp : Function.Injective p)
    {lam t delta : ℝ} {n : ℕ}
    (hcap : AngleCap p lam)
    (hn : 3 ≤ n)
    (hcard : 4 ≤ Fintype.card V)
    (hdelta0 : 0 ≤ delta)
    (hdeltaHalf : delta < (1 : ℝ) / 2)
    (ht : t = (n : ℝ) + delta)
    (hlam : lam = Real.pi / t)
    (C : ∀ i : V, CentreProjectiveCycle hp i)
    (s : V)
    (hs : centreExponent (C s) t = n - 1) :
    ((Finset.univ : Finset V).filter
      (fun i => i ≠ s ∧ centreExponent (C i) t = n - 2)).card ≤ 1 := by
  classical
  apply Finset.card_le_one.mpr
  intro a ha b hb
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha hb
  by_contra hab
  exact no_two_next_exponents_beside_top_of_card_ge_four
    hp hcap hn hcard hdelta0 hdeltaHalf ht hlam C
    ha.1.symm hb.1.symm hab hs ha.2 hb.2

#print axioms no_two_top_exponents_with_third
#print axioms top_exponent_unique_of_card_ge_three
#print axioms no_two_next_exponents_beside_top_of_card_ge_four
#print axioms actual_top_exponent_layer_card_le_one
#print axioms actual_next_exponent_layer_card_le_one_of_top

end JSP000404Research
