import JSP000404Research.SharpSupportTwoMultiplicity
import JSP000404Research.FourCentreSharpReduction
import JSP000404Research.ConcreteSharpCentre
import Mathlib.Tactic

/-!
# Second-layer multiplicity around a top Sendov centre

Let s have exponent n-1.  Every exponent n-2 companion has quotient support
one or two.

* Two support-one companions are impossible by transition-arc packing:
  the sharp centre costs n and each support-one deficit-two centre costs n-1.
* Two support-two companions are impossible by the arbitrary-cardinality
  sharp-pinned cluster theorem.

Therefore among any three distinct exponent n-2 companions, two have the same
support type and yield a contradiction.

So a top exponent centre can have at most two second-layer companions in an
arbitrary finite configuration.  This is a genuine profile-level constraint,
not a Fin 4 terminal.
-/

namespace JSP000404Research

theorem no_two_supportOne_deficitTwo_around_top
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane}
    (hp : Function.Injective p)
    (hcap : AngleCap p lam)
    {lam t delta : ℝ} {n : ℕ}
    (hn : 3 ≤ n)
    (hdelta0 : 0 ≤ delta)
    (hdeltaHalf : delta < (1 : ℝ) / 2)
    (ht : t = (n : ℝ) + delta)
    (hlam : lam = Real.pi / t)
    {s a b : V}
    (hsa : s ≠ a) (hsb : s ≠ b) (hab : a ≠ b)
    (Cs : CentreProjectiveCycle hp s)
    (Ca : CentreProjectiveCycle hp a)
    (Cb : CentreProjectiveCycle hp b)
    (hS : centreExponent Cs t = n - 1)
    (hA : centreExponent Ca t = n - 2)
    (hB : centreExponent Cb t = n - 2)
    (hsupA :
      positiveSupport (centreQuotient Ca t) = 1)
    (hsupB :
      positiveSupport (centreQuotient Cb t) = 1) :
    False := by
  have hdelta1 : delta < 1 := by linarith
  let HS :=
    Classical.choice
      (exists_highExponentTransitionIntervalCertificate
        hp hcap (by omega : 1 ≤ n)
        hdelta0 hdelta1 ht hlam
        s Cs (by rw [hS]; omega))
  let HA :=
    Classical.choice
      (exists_highExponentTransitionIntervalCertificate
        hp hcap (by omega : 1 ≤ n)
        hdelta0 hdelta1 ht hlam
        a Ca (by rw [hA]; omega))
  let HB :=
    Classical.choice
      (exists_highExponentTransitionIntervalCertificate
        hp hcap (by omega : 1 ≤ n)
        hdelta0 hdelta1 ht hlam
        b Cb (by rw [hB]; omega))
  exact no_sharp_with_two_support_one_deficit_two
    hp hn hdelta0 hdeltaHalf ht
    hsa hsb hab
    Cs Ca Cb HS HA HB
    hS hA hB hsupA hsupB

theorem no_top_with_three_deficitTwo_companions
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane}
    (hp : Function.Injective p)
    (hcap : AngleCap p lam)
    {lam t delta : ℝ} {n : ℕ}
    (hn : 3 ≤ n)
    (hdelta0 : 0 ≤ delta)
    (hdeltaHalf : delta < (1 : ℝ) / 2)
    (ht : t = (n : ℝ) + delta)
    (hlam : lam = Real.pi / t)
    {s a b c : V}
    (hsa : s ≠ a) (hsb : s ≠ b) (hsc : s ≠ c)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (Cs : CentreProjectiveCycle hp s)
    (Ca : CentreProjectiveCycle hp a)
    (Cb : CentreProjectiveCycle hp b)
    (Cc : CentreProjectiveCycle hp c)
    (hS : centreExponent Cs t = n - 1)
    (hA : centreExponent Ca t = n - 2)
    (hB : centreExponent Cb t = n - 2)
    (hC : centreExponent Cc t = n - 2) :
    False := by
  have hdelta1 : delta < 1 := by linarith
  have hs :
      SharpAt p delta lam s :=
    concrete_unit_deficit_is_sharp
      hp hcap (by omega : 2 ≤ n)
      hdelta0 hdelta1 ht hlam
      s Cs hS
  have hsupA :=
    deficit_two_support_one_or_two_concrete
      Ca hn hdelta0 hdeltaHalf ht hA
  have hsupB :=
    deficit_two_support_one_or_two_concrete
      Cb hn hdelta0 hdeltaHalf ht hB
  have hsupC :=
    deficit_two_support_one_or_two_concrete
      Cc hn hdelta0 hdeltaHalf ht hC
  rcases hsupA with hA1 | hA2 <;>
    rcases hsupB with hB1 | hB2 <;>
      rcases hsupC with hC1 | hC2
  · exact no_two_supportOne_deficitTwo_around_top
      hp hcap hn hdelta0 hdeltaHalf ht hlam
      hsa hsb hab Cs Ca Cb hS hA hB hA1 hB1
  · exact no_two_supportOne_deficitTwo_around_top
      hp hcap hn hdelta0 hdeltaHalf ht hlam
      hsa hsb hab Cs Ca Cb hS hA hB hA1 hB1
  · exact no_two_supportOne_deficitTwo_around_top
      hp hcap hn hdelta0 hdeltaHalf ht hlam
      hsa hsc hac Cs Ca Cc hS hA hC hA1 hC1
  · exact no_two_supportTwo_deficitTwo_around_sharp
      hp hcap hn hdelta0 hdeltaHalf ht hlam
      hsb hsc hsa hbc hab.symm hac.symm
      hs Cb Cc hB hC hB2 hC2
  · exact no_two_supportOne_deficitTwo_around_top
      hp hcap hn hdelta0 hdeltaHalf ht hlam
      hsb hsc hbc Cs Cb Cc hS hB hC hB1 hC1
  · exact no_two_supportTwo_deficitTwo_around_sharp
      hp hcap hn hdelta0 hdeltaHalf ht hlam
      hsa hsc hsb hac hab hbc.symm
      hs Ca Cc hA hC hA2 hC2
  · exact no_two_supportTwo_deficitTwo_around_sharp
      hp hcap hn hdelta0 hdeltaHalf ht hlam
      hsa hsb hsc hab hac hbc
      hs Ca Cb hA hB hA2 hB2
  · exact no_two_supportTwo_deficitTwo_around_sharp
      hp hcap hn hdelta0 hdeltaHalf ht hlam
      hsa hsb hsc hab hac hbc
      hs Ca Cb hA hB hA2 hB2


/-- Cardinal form: relative to one fixed top centre, at most two other centres
can lie in the second exponent layer. -/
theorem secondLayer_companion_card_le_two
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane}
    (hp : Function.Injective p)
    (hcap : AngleCap p lam)
    {lam t delta : ℝ} {n : ℕ}
    (hn : 3 ≤ n)
    (hdelta0 : 0 ≤ delta)
    (hdeltaHalf : delta < (1 : ℝ) / 2)
    (ht : t = (n : ℝ) + delta)
    (hlam : lam = Real.pi / t)
    (C : ∀ i : V, CentreProjectiveCycle hp i)
    (s : V)
    (hS : centreExponent (C s) t = n - 1) :
    ((Finset.univ : Finset V).filter
      (fun i => i ≠ s ∧
        centreExponent (C i) t = n - 2)).card ≤ 2 := by
  classical
  let S : Finset V :=
    (Finset.univ : Finset V).filter
      (fun i => i ≠ s ∧
        centreExponent (C i) t = n - 2)
  by_contra hcard
  have hgt : 2 < S.card := by omega
  rcases (Finset.two_lt_card.mp hgt) with
    ⟨a, ha, b, hb, c, hc, hab, hac, hbc⟩
  have ha' :
      a ≠ s ∧ centreExponent (C a) t = n - 2 := by
    simpa [S] using ha
  have hb' :
      b ≠ s ∧ centreExponent (C b) t = n - 2 := by
    simpa [S] using hb
  have hc' :
      c ≠ s ∧ centreExponent (C c) t = n - 2 := by
    simpa [S] using hc
  exact no_top_with_three_deficitTwo_companions
    hp hcap hn hdelta0 hdeltaHalf ht hlam
    ha'.1.symm hb'.1.symm hc'.1.symm
    hab hac hbc
    (C s) (C a) (C b) (C c)
    hS ha'.2 hb'.2 hc'.2

#print axioms secondLayer_companion_card_le_two

#print axioms no_two_supportOne_deficitTwo_around_top
#print axioms no_top_with_three_deficitTwo_companions

end JSP000404Research
