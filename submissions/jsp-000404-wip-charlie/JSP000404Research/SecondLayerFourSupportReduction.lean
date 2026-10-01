import JSP000404Research.SecondLayerNoTopReduction
import JSP000404Research.HighExponentTransitionPacking
import Mathlib.Data.Matrix.Notation
import Mathlib.Tactic

/-!
# Four-centre second-layer support reduction down to n = 3

The existing no-top reduction excludes three support-one second-layer centres
for n >= 4.  At n = 3 the three-centre quotient packing is exactly saturated:
3 * (n-1) = 2n = 6.

A fourth second-layer centre removes this equality case.  Its transition
quotient is positive, so three support-one centres plus the fourth centre
would contribute at least 7, contradicting the same global 2n packing bound.

Hence for every n >= 3, any four distinct second-layer centres contain at
least two support-two centres.
-/

namespace JSP000404Research

open scoped BigOperators

theorem four_transition_quotient_sum_le_two_n
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane}
    (hp : Function.Injective p)
    {t delta : ℝ} {n : ℕ}
    (hn : 1 ≤ n)
    (hdelta0 : 0 ≤ delta)
    (hdeltaHalf : delta < (1 : ℝ) / 2)
    (ht : t = (n : ℝ) + delta)
    {a b c d : V}
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d)
    (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d)
    (Ca : CentreProjectiveCycle hp a)
    (Cb : CentreProjectiveCycle hp b)
    (Cc : CentreProjectiveCycle hp c)
    (Cd : CentreProjectiveCycle hp d)
    (certA : HighExponentTransitionIntervalCertificate hp t a Ca)
    (certB : HighExponentTransitionIntervalCertificate hp t b Cb)
    (certC : HighExponentTransitionIntervalCertificate hp t c Cc)
    (certD : HighExponentTransitionIntervalCertificate hp t d Cd) :
    certA.qe + certB.qe + certC.qe + certD.qe ≤ 2 * n := by
  let centre : Fin 4 → V := ![a,b,c,d]
  have hcentre : Function.Injective centre := by
    intro x y hxy
    fin_cases x <;> fin_cases y <;>
      simp [centre] at hxy ⊢
    · exact False.elim (hab hxy)
    · exact False.elim (hac hxy)
    · exact False.elim (had hxy)
    · exact False.elim (hab hxy.symm)
    · exact False.elim (hbc hxy)
    · exact False.elim (hbd hxy)
    · exact False.elim (hac hxy.symm)
    · exact False.elim (hbc hxy.symm)
    · exact False.elim (hcd hxy)
    · exact False.elim (had hxy.symm)
    · exact False.elim (hbd hxy.symm)
    · exact False.elim (hcd hxy.symm)
  let C : ∀ r : Fin 4, CentreProjectiveCycle hp (centre r) :=
    fun r => by
      fin_cases r
      · simpa [centre] using Ca
      · simpa [centre] using Cb
      · simpa [centre] using Cc
      · simpa [centre] using Cd
  let cert : ∀ r : Fin 4,
      HighExponentTransitionIntervalCertificate hp t (centre r) (C r) :=
    fun r => by
      fin_cases r
      · simpa [centre,C] using certA
      · simpa [centre,C] using certB
      · simpa [centre,C] using certC
      · simpa [centre,C] using certD
  have h :=
    highTransition_quotient_sum_le_two_n
      hp hn hdelta0 hdeltaHalf ht
      centre hcentre C cert
  simpa [cert,C,centre,Fin.sum_univ_succ] using h

theorem no_three_supportOne_secondLayer_among_four_n3
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane}
    (hp : Function.Injective p)
    (hcap : AngleCap p lam)
    {lam t delta : ℝ}
    (hdelta0 : 0 ≤ delta)
    (hdeltaHalf : delta < (1 : ℝ) / 2)
    (ht : t = (3 : ℝ) + delta)
    (hlam : lam = Real.pi / t)
    {a b c d : V}
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d)
    (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d)
    (Ca : CentreProjectiveCycle hp a)
    (Cb : CentreProjectiveCycle hp b)
    (Cc : CentreProjectiveCycle hp c)
    (Cd : CentreProjectiveCycle hp d)
    (haSecond : centreExponent Ca t = 1)
    (hbSecond : centreExponent Cb t = 1)
    (hcSecond : centreExponent Cc t = 1)
    (hdSecond : centreExponent Cd t = 1)
    (haSupport : positiveSupport (centreQuotient Ca t) = 1)
    (hbSupport : positiveSupport (centreQuotient Cb t) = 1)
    (hcSupport : positiveSupport (centreQuotient Cc t) = 1) :
    False := by
  let hdelta1 : delta < 1 := by linarith
  let certA :=
    Classical.choice
      (exists_highExponentTransitionIntervalCertificate
        hp hcap (by omega : 1 ≤ 3)
        hdelta0 hdelta1 ht hlam
        a Ca (by rw [haSecond]))
  let certB :=
    Classical.choice
      (exists_highExponentTransitionIntervalCertificate
        hp hcap (by omega : 1 ≤ 3)
        hdelta0 hdelta1 ht hlam
        b Cb (by rw [hbSecond]))
  let certC :=
    Classical.choice
      (exists_highExponentTransitionIntervalCertificate
        hp hcap (by omega : 1 ≤ 3)
        hdelta0 hdelta1 ht hlam
        c Cc (by rw [hcSecond]))
  let certD :=
    Classical.choice
      (exists_highExponentTransitionIntervalCertificate
        hp hcap (by omega : 1 ≤ 3)
        hdelta0 hdelta1 ht hlam
        d Cd (by rw [hdSecond]))
  have hqa :
      certA.qe = 2 :=
    deficit_two_support_one_transition_qe_eq
      Ca certA (by omega : 3 ≤ 3)
      (by simpa using haSecond) haSupport
  have hqb :
      certB.qe = 2 :=
    deficit_two_support_one_transition_qe_eq
      Cb certB (by omega : 3 ≤ 3)
      (by simpa using hbSecond) hbSupport
  have hqc :
      certC.qe = 2 :=
    deficit_two_support_one_transition_qe_eq
      Cc certC (by omega : 3 ≤ 3)
      (by simpa using hcSecond) hcSupport
  have hqd : 1 ≤ certD.qe :=
    Nat.one_le_iff_ne_zero.mpr certD.qe_ne
  have hpack :=
    four_transition_quotient_sum_le_two_n
      hp (by omega : 1 ≤ 3)
      hdelta0 hdeltaHalf ht
      hab hac had hbc hbd hcd
      Ca Cb Cc Cd certA certB certC certD
  rw [hqa,hqb,hqc] at hpack
  omega

theorem four_secondLayer_has_two_supportTwo_of_three_le_n
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane}
    (hp : Function.Injective p)
    (hcap : AngleCap p lam)
    {lam t delta : ℝ} {n : ℕ}
    (hn3 : 3 ≤ n)
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
  by_cases hn4 : 4 ≤ n
  · exact four_secondLayer_has_two_supportTwo
      hp hcap hn4 hdelta0 hdeltaHalf ht hlam C
      hab hac had hbc hbd hcd
      haSecond hbSecond hcSecond hdSecond
  · have hnEq : n = 3 := by omega
    subst n
    have ha :=
      deficit_two_support_one_or_two_concrete
        (C a) (by omega : 3 ≤ 3)
        hdelta0 hdeltaHalf ht haSecond
    have hb :=
      deficit_two_support_one_or_two_concrete
        (C b) (by omega : 3 ≤ 3)
        hdelta0 hdeltaHalf ht hbSecond
    have hc :=
      deficit_two_support_one_or_two_concrete
        (C c) (by omega : 3 ≤ 3)
        hdelta0 hdeltaHalf ht hcSecond
    have hd :=
      deficit_two_support_one_or_two_concrete
        (C d) (by omega : 3 ≤ 3)
        hdelta0 hdeltaHalf ht hdSecond
    rcases ha with ha1 | ha2 <;>
      rcases hb with hb1 | hb2 <;>
      rcases hc with hc1 | hc2 <;>
      rcases hd with hd1 | hd2
    · exact False.elim
        (no_three_supportOne_secondLayer_among_four_n3
          hp hcap hdelta0 hdeltaHalf ht hlam
          hab hac had hbc hbd hcd
          (C a) (C b) (C c) (C d)
          haSecond hbSecond hcSecond hdSecond ha1 hb1 hc1)
    · exact False.elim
        (no_three_supportOne_secondLayer_among_four_n3
          hp hcap hdelta0 hdeltaHalf ht hlam
          hab hac had hbc hbd hcd
          (C a) (C b) (C c) (C d)
          haSecond hbSecond hcSecond hdSecond ha1 hb1 hc1)
    · exact False.elim
        (no_three_supportOne_secondLayer_among_four_n3
          hp hcap hdelta0 hdeltaHalf ht hlam
          hab hac had hbc hbd hcd
          (C a) (C b) (C d) (C c)
          haSecond hbSecond hdSecond hcSecond ha1 hb1 hd1)
    · exact ⟨c,d,hcd,by simp,by simp,hc2,hd2⟩
    · exact False.elim
        (no_three_supportOne_secondLayer_among_four_n3
          hp hcap hdelta0 hdeltaHalf ht hlam
          hac hab had hbc.symm hcd hbd
          (C a) (C c) (C d) (C b)
          haSecond hcSecond hdSecond hbSecond ha1 hc1 hd1)
    · exact ⟨b,d,hbd,by simp,by simp,hb2,hd2⟩
    · exact ⟨b,c,hbc,by simp,by simp,hb2,hc2⟩
    · exact ⟨b,c,hbc,by simp,by simp,hb2,hc2⟩
    · exact False.elim
        (no_three_supportOne_secondLayer_among_four_n3
          hp hcap hdelta0 hdeltaHalf ht hlam
          hbc hab.symm hbd hac.symm hcd had
          (C b) (C c) (C d) (C a)
          hbSecond hcSecond hdSecond haSecond hb1 hc1 hd1)
    · exact ⟨a,d,had,by simp,by simp,ha2,hd2⟩
    · exact ⟨a,c,hac,by simp,by simp,ha2,hc2⟩
    · exact ⟨a,c,hac,by simp,by simp,ha2,hc2⟩
    · exact ⟨a,b,hab,by simp,by simp,ha2,hb2⟩
    · exact ⟨a,b,hab,by simp,by simp,ha2,hb2⟩
    · exact ⟨a,b,hab,by simp,by simp,ha2,hb2⟩
    · exact ⟨a,b,hab,by simp,by simp,ha2,hb2⟩

#print axioms four_transition_quotient_sum_le_two_n
#print axioms no_three_supportOne_secondLayer_among_four_n3
#print axioms four_secondLayer_has_two_supportTwo_of_three_le_n

end JSP000404Research
