import JSP000404Research.FourCentreTransitionCases
import Mathlib.Data.Matrix.Notation
import Mathlib.Tactic

/-!
# Uniform four-second-layer support-two reduction

The earlier three-centre reduction needed n >= 4 because three support-one
second-layer centres contribute exactly 2n when n=3.  Keeping a fourth
second-layer centre removes this equality case: its transition certificate
has positive quotient, so the four-centre sum is at least

  3 * (n - 1) + 1 = 3n - 2 > 2n

for every n >= 3.

Hence every four distinct second-layer centres contain two distinct
support-two centres, uniformly for all n >= 3.
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

theorem no_three_supportOne_among_four_secondLayer
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
    {a b c d : V}
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d)
    (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d)
    (Ca : CentreProjectiveCycle hp a)
    (Cb : CentreProjectiveCycle hp b)
    (Cc : CentreProjectiveCycle hp c)
    (Cd : CentreProjectiveCycle hp d)
    (haSecond : centreExponent Ca t = n - 2)
    (hbSecond : centreExponent Cb t = n - 2)
    (hcSecond : centreExponent Cc t = n - 2)
    (hdSecond : centreExponent Cd t = n - 2)
    (haSupport : positiveSupport (centreQuotient Ca t) = 1)
    (hbSupport : positiveSupport (centreQuotient Cb t) = 1)
    (hcSupport : positiveSupport (centreQuotient Cc t) = 1) :
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
  let certD :=
    Classical.choice
      (exists_highExponentTransitionIntervalCertificate
        hp hcap (by omega : 1 ≤ n)
        hdelta0 hdelta1 ht hlam
        d Cd (by rw [hdSecond]))
  have hqA : certA.qe = n - 1 :=
    deficit_two_support_one_transition_qe_eq
      Ca certA hn3 haSecond haSupport
  have hqB : certB.qe = n - 1 :=
    deficit_two_support_one_transition_qe_eq
      Cb certB hn3 hbSecond hbSupport
  have hqC : certC.qe = n - 1 :=
    deficit_two_support_one_transition_qe_eq
      Cc certC hn3 hcSecond hcSupport
  have hqDpos : 1 ≤ certD.qe :=
    Nat.one_le_iff_ne_zero.mpr certD.qe_ne
  have hpack :=
    four_transition_quotient_sum_le_two_n
      hp (by omega : 1 ≤ n)
      hdelta0 hdeltaHalf ht
      hab hac had hbc hbd hcd
      Ca Cb Cc Cd certA certB certC certD
  rw [hqA,hqB,hqC] at hpack
  omega

theorem four_secondLayer_has_two_supportTwo_uniform
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
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d)
    (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d)
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
      (C a) hn3 hdelta0 hdeltaHalf ht haSecond
  have hb :=
    deficit_two_support_one_or_two_concrete
      (C b) hn3 hdelta0 hdeltaHalf ht hbSecond
  have hc :=
    deficit_two_support_one_or_two_concrete
      (C c) hn3 hdelta0 hdeltaHalf ht hcSecond
  have hd :=
    deficit_two_support_one_or_two_concrete
      (C d) hn3 hdelta0 hdeltaHalf ht hdSecond

  have hnoABC :
      ¬ (positiveSupport (centreQuotient (C a) t) = 1 ∧
         positiveSupport (centreQuotient (C b) t) = 1 ∧
         positiveSupport (centreQuotient (C c) t) = 1) := by
    rintro ⟨ha1,hb1,hc1⟩
    exact no_three_supportOne_among_four_secondLayer
      hp hcap hn3 hdelta0 hdeltaHalf ht hlam
      hab hac had hbc hbd hcd
      (C a) (C b) (C c) (C d)
      haSecond hbSecond hcSecond hdSecond ha1 hb1 hc1
  have hnoABD :
      ¬ (positiveSupport (centreQuotient (C a) t) = 1 ∧
         positiveSupport (centreQuotient (C b) t) = 1 ∧
         positiveSupport (centreQuotient (C d) t) = 1) := by
    rintro ⟨ha1,hb1,hd1⟩
    exact no_three_supportOne_among_four_secondLayer
      hp hcap hn3 hdelta0 hdeltaHalf ht hlam
      hab had hac hbd hbc hcd.symm
      (C a) (C b) (C d) (C c)
      haSecond hbSecond hdSecond hcSecond ha1 hb1 hd1
  have hnoACD :
      ¬ (positiveSupport (centreQuotient (C a) t) = 1 ∧
         positiveSupport (centreQuotient (C c) t) = 1 ∧
         positiveSupport (centreQuotient (C d) t) = 1) := by
    rintro ⟨ha1,hc1,hd1⟩
    exact no_three_supportOne_among_four_secondLayer
      hp hcap hn3 hdelta0 hdeltaHalf ht hlam
      hac had hab hcd hbc.symm hbd.symm
      (C a) (C c) (C d) (C b)
      haSecond hcSecond hdSecond hbSecond ha1 hc1 hd1
  have hnoBCD :
      ¬ (positiveSupport (centreQuotient (C b) t) = 1 ∧
         positiveSupport (centreQuotient (C c) t) = 1 ∧
         positiveSupport (centreQuotient (C d) t) = 1) := by
    rintro ⟨hb1,hc1,hd1⟩
    exact no_three_supportOne_among_four_secondLayer
      hp hcap hn3 hdelta0 hdeltaHalf ht hlam
      hbc hbd hab.symm hcd hac.symm had.symm
      (C b) (C c) (C d) (C a)
      hbSecond hcSecond hdSecond haSecond hb1 hc1 hd1

  rcases ha with ha1 | ha2 <;>
    rcases hb with hb1 | hb2 <;>
    rcases hc with hc1 | hc2 <;>
    rcases hd with hd1 | hd2
  · exact False.elim (hnoABC ⟨ha1,hb1,hc1⟩)
  · exact False.elim (hnoABC ⟨ha1,hb1,hc1⟩)
  · exact False.elim (hnoABD ⟨ha1,hb1,hd1⟩)
  · exact ⟨c,d,hcd,by simp,by simp,hc2,hd2⟩
  · exact False.elim (hnoACD ⟨ha1,hc1,hd1⟩)
  · exact ⟨b,d,hbd,by simp,by simp,hb2,hd2⟩
  · exact ⟨b,c,hbc,by simp,by simp,hb2,hc2⟩
  · exact ⟨b,c,hbc,by simp,by simp,hb2,hc2⟩
  · exact False.elim (hnoBCD ⟨hb1,hc1,hd1⟩)
  · exact ⟨a,d,had,by simp,by simp,ha2,hd2⟩
  · exact ⟨a,c,hac,by simp,by simp,ha2,hc2⟩
  · exact ⟨a,c,hac,by simp,by simp,ha2,hc2⟩
  · exact ⟨a,b,hab,by simp,by simp,ha2,hb2⟩
  · exact ⟨a,b,hab,by simp,by simp,ha2,hb2⟩
  · exact ⟨a,b,hab,by simp,by simp,ha2,hb2⟩
  · exact ⟨a,b,hab,by simp,by simp,ha2,hb2⟩

#print axioms four_transition_quotient_sum_le_two_n
#print axioms no_three_supportOne_among_four_secondLayer
#print axioms four_secondLayer_has_two_supportTwo_uniform

end JSP000404Research
