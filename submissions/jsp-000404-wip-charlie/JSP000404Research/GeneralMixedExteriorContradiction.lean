import JSP000404Research.ExposedSupportIntervalGeneral
import JSP000404Research.SupportIntervalRestriction
import JSP000404Research.FourPointConvexSeparation
import JSP000404Research.FourCentreTransitionCases
import Mathlib.Data.Matrix.Notation
import Mathlib.Tactic

/-!
# Cardinality-free mixed exterior contradiction by four-point restriction

Let s be a top centre, a a deficit-two/support-one centre, and b a
deficit-two/support-two centre in an arbitrary finite configuration.

Transition packing forces the three distinguished transition quotients to be

  n, n-1, 1.

Thus their support arcs already contribute at least 2n*lambda.

For any fourth point c outside conv{s,a,b}, restrict the full configuration to
the four points s,a,b,c.  The three global support certificates restrict
unchanged.  Hahn--Banach strictly exposes c in this four-point
subconfiguration, and the cardinality-free exposed-support theorem gives c a
support arc of turn at least lambda.

The four restricted support arcs would therefore have total turn at least

  (2n+1)*lambda > 2*pi

because t=n+delta and delta<1/2, contradicting support-arc packing.
-/

namespace JSP000404Research

open Real

theorem no_mixed_fourth_outside_triangle
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
    (hS : centreExponent Cs t = n - 1)
    (hA : centreExponent Ca t = n - 2)
    (hB : centreExponent Cb t = n - 2)
    (hsupA :
      positiveSupport (centreQuotient Ca t) = 1)
    (hsupB :
      positiveSupport (centreQuotient Cb t) = 2)
    (hout :
      p c ∉ convexHull ℝ
        ({p s, p a, p b} : Set Plane)) :
    False := by
  have hdelta1 : delta < 1 := by linarith
  have htpos :
      0 < t :=
    sendov_scale_pos (by omega : 1 ≤ n) hdelta0 ht
  have htone : 1 ≤ t := by
    rw [ht]
    have hnR : (3 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  have hlampos : 0 < lam := by
    rw [hlam]
    exact div_pos Real.pi_pos htpos

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

  have hqS : HS.qe = n :=
    unit_deficit_transition_qe_eq_n
      Cs HS (by omega) hdelta0 hdelta1 ht hS
  have hqA : HA.qe = n - 1 :=
    deficit_two_support_one_transition_qe_eq
      Ca HA hn hA hsupA
  have hqB : HB.qe = 1 :=
    mixed_deficit_two_transition_qe_eq_one
      hp hn hdelta0 hdeltaHalf ht
      hsa hsb hab
      Cs Ca Cb HS HA HB
      hS hA hsupA

  let SS : SupportIntervalCertificate (p := p) s :=
    SupportIntervalCertificate.ofHighExponent HS
  let SA : SupportIntervalCertificate (p := p) a :=
    SupportIntervalCertificate.ofHighExponent HA
  let SB : SupportIntervalCertificate (p := p) b :=
    SupportIntervalCertificate.ofHighExponent HB

  have hturnS :
      (n : ℝ) * lam ≤ SS.turnLength := by
    have h :=
      SupportIntervalCertificate.qe_mul_lam_le_turnLength_ofHighExponent
        HS htpos hlam
    rw [hqS] at h
    exact h
  have hturnA :
      ((n - 1 : ℕ) : ℝ) * lam ≤ SA.turnLength := by
    have h :=
      SupportIntervalCertificate.qe_mul_lam_le_turnLength_ofHighExponent
        HA htpos hlam
    rw [hqA] at h
    exact h
  have hturnB :
      lam ≤ SB.turnLength := by
    have h :=
      SupportIntervalCertificate.qe_mul_lam_le_turnLength_ofHighExponent
        HB htpos hlam
    rw [hqB] at h
    simpa using h

  let e : Fin 4 → V := ![s, a, b, c]
  have he : Function.Injective e := by
    intro x y hxy
    fin_cases x <;> fin_cases y <;>
      simp [e] at hxy ⊢ <;>
      try { exact False.elim (hsa hxy) } <;>
      try { exact False.elim (hsb hxy) } <;>
      try { exact False.elim (hsc hxy) } <;>
      try { exact False.elim (hab hxy) } <;>
      try { exact False.elim (hac hxy) } <;>
      try { exact False.elim (hbc hxy) } <;>
      try { exact False.elim (hsa hxy.symm) } <;>
      try { exact False.elim (hsb hxy.symm) } <;>
      try { exact False.elim (hsc hxy.symm) } <;>
      try { exact False.elim (hab hxy.symm) } <;>
      try { exact False.elim (hac hxy.symm) } <;>
      try { exact False.elim (hbc hxy.symm) }

  let p4 : Fin 4 → Plane := fun r => p (e r)
  have hp4 : Function.Injective p4 :=
    hp.comp he
  have hcap4 : AngleCap p4 lam := by
    intro x y z hxy hxz hyz
    exact hcap (e x) (e y) (e z)
      (he.ne hxy) (he.ne hxz) (he.ne hyz)

  have hout4 :
      p4 3 ∉ convexHull ℝ
        ({p4 0, p4 1, p4 2} : Set Plane) := by
    simpa [p4, e] using hout

  have hExpose4 :
      StrictlyExposedAt p4 (3 : Fin 4) :=
    strictlyExposedAt_of_not_mem_other_triangle_fin_four
      hp4
      (by decide : (0 : Fin 4) ≠ 1)
      (by decide : (0 : Fin 4) ≠ 2)
      (by decide : (0 : Fin 4) ≠ 3)
      (by decide : (1 : Fin 4) ≠ 2)
      (by decide : (1 : Fin 4) ≠ 3)
      (by decide : (2 : Fin 4) ≠ 3)
      hout4

  have hother4 : Nonempty (OtherVertex (3 : Fin 4)) :=
    ⟨⟨0, by decide⟩⟩
  let C4 : CentreProjectiveCycle hp4 (3 : Fin 4) :=
    Classical.choice
      (exists_centreProjectiveCycle hp4 3 hother4)

  obtain ⟨SC, hturnC⟩ :=
    exists_supportIntervalCertificate_of_strictlyExposed
      hp4 hcap4 htpos htone hlam C4 hExpose4

  let SS4 : SupportIntervalCertificate (p := p4) (0 : Fin 4) := by
    simpa [p4, e, SS] using
      (SupportIntervalCertificate.restrictOfInjective
        e he (0 : Fin 4) SS)
  let SA4 : SupportIntervalCertificate (p := p4) (1 : Fin 4) := by
    simpa [p4, e, SA] using
      (SupportIntervalCertificate.restrictOfInjective
        e he (1 : Fin 4) SA)
  let SB4 : SupportIntervalCertificate (p := p4) (2 : Fin 4) := by
    simpa [p4, e, SB] using
      (SupportIntervalCertificate.restrictOfInjective
        e he (2 : Fin 4) SB)

  have hpack :=
    SupportIntervalCertificate.four_turnLength_sum_le_two_pi
      (p := p4)
      (by decide : (0 : Fin 4) ≠ 1)
      (by decide : (0 : Fin 4) ≠ 2)
      (by decide : (0 : Fin 4) ≠ 3)
      (by decide : (1 : Fin 4) ≠ 2)
      (by decide : (1 : Fin 4) ≠ 3)
      (by decide : (2 : Fin 4) ≠ 3)
      SS4 SA4 SB4 SC

  have hS4 : (n : ℝ) * lam ≤ SS4.turnLength := by
    simpa [SS4, SS, p4, e] using hturnS
  have hA4 :
      ((n - 1 : ℕ) : ℝ) * lam ≤ SA4.turnLength := by
    simpa [SA4, SA, p4, e] using hturnA
  have hB4 : lam ≤ SB4.turnLength := by
    simpa [SB4, SB, p4, e] using hturnB

  have hncast :
      ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
    exact_mod_cast (Nat.sub_add_cancel (by omega : 1 ≤ n))
  have hpi : Real.pi = t * lam := by
    rw [hlam]
    field_simp [ne_of_gt htpos]

  dsimp [SS4, SA4, SB4] at hpack hS4 hA4 hB4
  rw [hncast] at hA4
  nlinarith

#print axioms no_mixed_fourth_outside_triangle

end JSP000404Research
