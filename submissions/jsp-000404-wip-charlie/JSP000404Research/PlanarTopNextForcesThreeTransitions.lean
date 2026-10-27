import JSP000404Research.SupportThreeTransitionDichotomy
import JSP000404Research.TopNextSupportOneFourCentrePacking
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic

/-!
# Source-native top+next forces the three-transition regime

At n=3, a real top exponent-two centre and a real exponent-one
support-one centre jointly spend 3+2 of the six strict support
transition quotients. Two further distinct original centres whose
ACTUAL canonical sign paths have exactly ONE sign transition
would each yield a positive transition certificate and exceed the
six-unit budget.

Hence these configurations admit at most ONE further one-transition
centre, independent of that centre's quotient support. In particular
among the >=4 high-support centres forced by the existing top+next
packing, all but at most one are necessarily in the 3-transition
branch of the exact support-three dichotomy.

This is an unconditional original-plane geometric obstruction
under the displayed genuine top+next hypotheses, NOT the missing
global eight-source Boolean-hole payment.
-/

namespace JSP000404Research
open scoped BigOperators

/-- Any REAL centre with exactly one canonical sign transition has
a positive strict-support interval certificate. The certificate
is constructed from the original geometric rays and their genuine
positive quotient gap, not from a synthetic carrier. -/
theorem actual_one_transition_has_positive_certificate
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane}
    (hp : Function.Injective p)
    {lam t : ℝ}
    (hcap : AngleCap p lam)
    (htpos : 0 < t) (htone : 1 ≤ t)
    (hlam : lam = Real.pi / t)
    (i : V) (C : CentreProjectiveCycle hp i)
    (first : OtherVertex i)
    (rest : List (OtherVertex i))
    (hrays : C.rays = first :: rest)
    (htrans :
      boolTransitionCountFrom
        (raySignAt hp i first)
        (liftedCentreSignPath hp i first rest) = 1) :
    ∃ H : HighExponentTransitionIntervalCertificate hp t i C,
      H.qe ≠ 0 := by
  have hchanges :
      ChangesOnlyOnPositive
        (raySignAt hp i first)
        (liftedCentreSignPath hp i first rest)
        (quotientList t C.gaps) :=
    centre_changesOnlyOnPositive
      hp hcap htpos htone hlam i C first rest hrays
  obtain ⟨pre,post,qe,hqe,hq,hsign⟩ :=
    one_transition_positive_gap_decomposition
      (raySignAt hp i first)
      (liftedCentreSignPath hp i first rest)
      (quotientList t C.gaps)
      hchanges htrans
  obtain ⟨H, hHqe⟩ :=
    exists_highExponentTransitionIntervalCertificate_of_decomposition
      hp htpos i C first rest pre post qe
      hrays hqe hq hsign
  refine ⟨H, ?_⟩
  rw [hHqe]
  exact hqe

/-- Four distinct ORIGINAL centres cannot consist of a top,
a next support-one, and two other actual one-transition centres
at the n=3 lower-half strip. The two extra centres need NOT have
support <=2; hence this genuinely extends the existing low-support
four-centre packing obstruction into the support-three regime. -/
theorem planar_three_top_next_no_two_one_transition_centres
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane}
    (hp : Function.Injective p)
    {lam t delta : ℝ}
    (hcap : AngleCap p lam)
    (hdelta0 : 0 ≤ delta)
    (hdeltaHalf : delta < (1 : ℝ) / 2)
    (ht : t = (3 : ℝ) + delta)
    (hlam : lam = Real.pi / t)
    {s a b c : V}
    (hsa : s ≠ a) (hsb : s ≠ b) (hsc : s ≠ c)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (Cs : CentreProjectiveCycle hp s)
    (Ca : CentreProjectiveCycle hp a)
    (Cb : CentreProjectiveCycle hp b)
    (Cc : CentreProjectiveCycle hp c)
    (hS : centreExponent Cs t = 2)
    (hA : centreExponent Ca t = 1)
    (hsupA : positiveSupport (centreQuotient Ca t) = 1)
    (fb : OtherVertex b) (rb : List (OtherVertex b))
    (frb : Cb.rays = fb :: rb)
    (htb : boolTransitionCountFrom (raySignAt hp b fb)
      (liftedCentreSignPath hp b fb rb) = 1)
    (fc : OtherVertex c) (rc : List (OtherVertex c))
    (frc : Cc.rays = fc :: rc)
    (htc : boolTransitionCountFrom (raySignAt hp c fc)
      (liftedCentreSignPath hp c fc rc) = 1) :
    False := by
  classical
  have hdelta1 : delta < 1 := by linarith
  have htpos : 0 < t :=
    sendov_scale_pos (by decide : 1 ≤ (3 : ℕ)) hdelta0 ht
  have htone : 1 ≤ t :=
    sendov_scale_one_le (by decide : 1 ≤ (3 : ℕ)) hdelta0 ht
  let HS := Classical.choice
    (exists_highExponentTransitionIntervalCertificate
      hp hcap (by decide : 1 ≤ (3 : ℕ))
      hdelta0 hdelta1 ht hlam
      s Cs (by rw [hS]; omega))
  obtain ⟨HA, hHApos⟩ :=
    exists_transitionIntervalCertificate_of_support_le_two
      hp hcap htpos htone hlam a Ca (by omega)
  obtain ⟨HB, hHBpos⟩ :=
    actual_one_transition_has_positive_certificate
      hp hcap htpos htone hlam b Cb fb rb frb htb
  obtain ⟨HC, hHCpos⟩ :=
    actual_one_transition_has_positive_certificate
      hp hcap htpos htone hlam c Cc fc rc frc htc
  have hqS : HS.qe = 3 :=
    top_exponent_transition_qe_eq_n Cs
      (by decide : 2 ≤ (3 : ℕ))
      hdelta0 hdelta1 ht hS HS
  have hqA : HA.qe = 2 := by
    have h := support_one_transitionInterval_qe_eq_exponent_add_one
      Ca HA hsupA
    rw [hA] at h
    omega
  let centre : Fin 4 → V := ![s,a,b,c]
  let Cfam : ∀ r : Fin 4,
      CentreProjectiveCycle hp (centre r) := by
    intro r
    rcases r with ⟨i, hi⟩
    interval_cases i
    · simpa [centre] using Cs
    · simpa [centre] using Ca
    · simpa [centre] using Cb
    · simpa [centre] using Cc
  let cert : ∀ r : Fin 4,
      HighExponentTransitionIntervalCertificate
        hp t (centre r) (Cfam r) := by
    intro r
    rcases r with ⟨i, hi⟩
    interval_cases i
    · simpa [centre, Cfam] using HS
    · simpa [centre, Cfam] using HA
    · simpa [centre, Cfam] using HB
    · simpa [centre, Cfam] using HC
  have hcentre : Function.Injective centre := by
    intro x y hxy
    fin_cases x <;> fin_cases y <;>
      simp [centre] at hxy ⊢ <;>
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
  have hpack :
      (∑ r : Fin 4, (cert r).qe) ≤ 2 * (3 : ℕ) :=
    highTransition_quotient_sum_le_two_n
      hp (by decide : 1 ≤ (3 : ℕ))
      hdelta0 hdeltaHalf ht
      centre hcentre Cfam cert
  have hcert0 : (cert (0 : Fin 4)).qe = HS.qe := by rfl
  have hcert1 : (cert (1 : Fin 4)).qe = HA.qe := by rfl
  have hcert2 : (cert (2 : Fin 4)).qe = HB.qe := by rfl
  have hcert3 : (cert (3 : Fin 4)).qe = HC.qe := by rfl
  have hpack' : HS.qe + HA.qe + HB.qe + HC.qe ≤ 6 := by
    simpa [Fin.sum_univ_succ, hcert0, hcert1, hcert2, hcert3,
      add_assoc] using hpack
  have hBpos : 1 ≤ HB.qe := Nat.one_le_iff_ne_zero.mpr hHBpos
  have hCpos : 1 ≤ HC.qe := Nat.one_le_iff_ne_zero.mpr hHCpos
  omega

#print axioms actual_one_transition_has_positive_certificate
#print axioms planar_three_top_next_no_two_one_transition_centres

end JSP000404Research
