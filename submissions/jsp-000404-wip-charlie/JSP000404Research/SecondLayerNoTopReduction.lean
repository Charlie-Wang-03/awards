import JSP000404Research.FourCentreTransitionCases
import JSP000404Research.DeficitTwo
import Mathlib.Tactic

/-!
# No-top reduction for four second-layer centres

For a deficit-two / second-layer centre, quotient support is either one or two.

Three distinct support-one second-layer centres are impossible when n >= 4:
each has transition quotient n-1, while the global three-centre transition
packing bound is 2n.

Consequently among any four distinct second-layer centres, at least two have
quotient support two.  This reduction does not assume a sharp/top centre.
-/

namespace JSP000404Research

theorem no_three_supportOne_secondLayer_of_four_le_n
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane}
    (hp : Function.Injective p)
    (hcap : AngleCap p lam)
    {lam t delta : ℝ} {n : ℕ}
    (hn4 : 4 ≤ n)
    (hdelta0 : 0 ≤ delta)
    (hdeltaHalf : delta < (1 : ℝ) / 2)
    (ht : t = (n : ℝ) + delta)
    (hlam : lam = Real.pi / t)
    {a b c : V}
    (hab : a ≠ b)
    (hac : a ≠ c)
    (hbc : b ≠ c)
    (Ca : CentreProjectiveCycle hp a)
    (Cb : CentreProjectiveCycle hp b)
    (Cc : CentreProjectiveCycle hp c)
    (haSecond : centreExponent Ca t = n - 2)
    (hbSecond : centreExponent Cb t = n - 2)
    (hcSecond : centreExponent Cc t = n - 2)
    (haSupport :
      positiveSupport (centreQuotient Ca t) = 1)
    (hbSupport :
      positiveSupport (centreQuotient Cb t) = 1)
    (hcSupport :
      positiveSupport (centreQuotient Cc t) = 1) :
    False := by
  let hdelta1 : delta < 1 := by linarith
  let certA :=
    Classical.choice
      (exists_highExponentTransitionIntervalCertificate
        hp hcap (by omega : 1 ≤ n)
        hdelta0 hdelta1 ht hlam
        a Ca (by rw [haSecond]))
  let certB :=
    Classical.choice
      (exists_highExponentTransitionIntervalCertificate
        hp hcap (by omega : 1 ≤ n)
        hdelta0 hdelta1 ht hlam
        b Cb (by rw [hbSecond]))
  let certC :=
    Classical.choice
      (exists_highExponentTransitionIntervalCertificate
        hp hcap (by omega : 1 ≤ n)
        hdelta0 hdelta1 ht hlam
        c Cc (by rw [hcSecond]))

  have hqa :
      certA.qe = n - 1 :=
    deficit_two_support_one_transition_qe_eq
      Ca certA (by omega : 3 ≤ n)
      haSecond haSupport
  have hqb :
      certB.qe = n - 1 :=
    deficit_two_support_one_transition_qe_eq
      Cb certB (by omega : 3 ≤ n)
      hbSecond hbSupport
  have hqc :
      certC.qe = n - 1 :=
    deficit_two_support_one_transition_qe_eq
      Cc certC (by omega : 3 ≤ n)
      hcSecond hcSupport

  have hpack :=
    three_transition_quotient_sum_le_two_n
      hp (by omega : 1 ≤ n)
      hdelta0 hdeltaHalf ht
      hab hac hbc
      Ca Cb Cc certA certB certC
  rw [hqa,hqb,hqc] at hpack
  omega

/-- Four distinct second-layer centres contain two distinct support-two
centres when n >= 4. -/
theorem four_secondLayer_has_two_supportTwo
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane}
    (hp : Function.Injective p)
    (hcap : AngleCap p lam)
    {lam t delta : ℝ} {n : ℕ}
    (hn4 : 4 ≤ n)
    (hdelta0 : 0 ≤ delta)
    (hdeltaHalf : delta < (1 : ℝ) / 2)
    (ht : t = (n : ℝ) + delta)
    (hlam : lam = Real.pi / t)
    (C : ∀ i : V, CentreProjectiveCycle hp i)
    {a b c d : V}
    (hab : a ≠ b)
    (hac : a ≠ c)
    (had : a ≠ d)
    (hbc : b ≠ c)
    (hbd : b ≠ d)
    (hcd : c ≠ d)
    (haSecond : centreExponent (C a) t = n - 2)
    (hbSecond : centreExponent (C b) t = n - 2)
    (hcSecond : centreExponent (C c) t = n - 2)
    (hdSecond : centreExponent (C d) t = n - 2) :
    ∃ x y : V,
      x ≠ y ∧
      x ∈ ({a,b,c,d} : Finset V) ∧
      y ∈ ({a,b,c,d} : Finset V) ∧
      positiveSupport (centreQuotient (C x) t) = 2 ∧
      positiveSupport (centreQuotient (C y) t) = 2 := by
  have ha :=
    deficit_two_support_one_or_two_concrete
      (C a) (by omega : 3 ≤ n)
      hdelta0 hdeltaHalf ht haSecond
  have hb :=
    deficit_two_support_one_or_two_concrete
      (C b) (by omega : 3 ≤ n)
      hdelta0 hdeltaHalf ht hbSecond
  have hc :=
    deficit_two_support_one_or_two_concrete
      (C c) (by omega : 3 ≤ n)
      hdelta0 hdeltaHalf ht hcSecond
  have hd :=
    deficit_two_support_one_or_two_concrete
      (C d) (by omega : 3 ≤ n)
      hdelta0 hdeltaHalf ht hdSecond
  rcases ha with ha1 | ha2 <;>
    rcases hb with hb1 | hb2 <;>
    rcases hc with hc1 | hc2 <;>
    rcases hd with hd1 | hd2
  · exact False.elim
      (no_three_supportOne_secondLayer_of_four_le_n
        hp hcap hn4 hdelta0 hdeltaHalf ht hlam
        hab hac hbc (C a) (C b) (C c)
        haSecond hbSecond hcSecond ha1 hb1 hc1)
  · exact False.elim
      (no_three_supportOne_secondLayer_of_four_le_n
        hp hcap hn4 hdelta0 hdeltaHalf ht hlam
        hab hac hbc (C a) (C b) (C c)
        haSecond hbSecond hcSecond ha1 hb1 hc1)
  · exact False.elim
      (no_three_supportOne_secondLayer_of_four_le_n
        hp hcap hn4 hdelta0 hdeltaHalf ht hlam
        hab had hbd (C a) (C b) (C d)
        haSecond hbSecond hdSecond ha1 hb1 hd1)
  · exact ⟨c,d,hcd,by simp,by simp,hc2,hd2⟩
  · exact False.elim
      (no_three_supportOne_secondLayer_of_four_le_n
        hp hcap hn4 hdelta0 hdeltaHalf ht hlam
        hac had hcd (C a) (C c) (C d)
        haSecond hcSecond hdSecond ha1 hc1 hd1)
  · exact ⟨b,d,hbd,by simp,by simp,hb2,hd2⟩
  · exact ⟨b,c,hbc,by simp,by simp,hb2,hc2⟩
  · exact ⟨b,c,hbc,by simp,by simp,hb2,hc2⟩
  · exact False.elim
      (no_three_supportOne_secondLayer_of_four_le_n
        hp hcap hn4 hdelta0 hdeltaHalf ht hlam
        hbc hbd hcd (C b) (C c) (C d)
        hbSecond hcSecond hdSecond hb1 hc1 hd1)
  · exact ⟨a,d,had,by simp,by simp,ha2,hd2⟩
  · exact ⟨a,c,hac,by simp,by simp,ha2,hc2⟩
  · exact ⟨a,c,hac,by simp,by simp,ha2,hc2⟩
  · exact ⟨a,b,hab,by simp,by simp,ha2,hb2⟩
  · exact ⟨a,b,hab,by simp,by simp,ha2,hb2⟩
  · exact ⟨a,b,hab,by simp,by simp,ha2,hb2⟩
  · exact ⟨a,b,hab,by simp,by simp,ha2,hb2⟩

#print axioms no_three_supportOne_secondLayer_of_four_le_n
#print axioms four_secondLayer_has_two_supportTwo

end JSP000404Research
