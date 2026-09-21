import JSP000404Research.SupportIntervalCertificate
import Mathlib.Tactic

/-!
# Mixed four-centre exterior support contradiction

In the mixed sharp-layer configuration the three high-exponent centres have
transition quotients

  n, n-1, 1,

hence total transition cost 2n.

Each high transition certificate gives a disjoint dual strict-support arc whose
length is at least qe*lambda.  If the fourth point also admits any common-signed
support certificate with dual turn length at least lambda, the four disjoint
support arcs have total length at least

  (2n+1)*lambda.

But the whole direction circle has length

  2*pi = 2*(n+delta)*lambda,

and delta<1/2 makes the former strictly larger.  Contradiction.

Thus in the remaining mixed four-centre case, the fourth point cannot carry a
full cap-unit of strict-support turn.  A geometric hull/interior dichotomy may
therefore send the other branch directly to FourCentreMixedInteriorArithmetic.
-/

namespace JSP000404Research

open Real

theorem no_mixed_fourth_support_arc_of_one_cap_unit
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane} {hp : Function.Injective p}
    {s a b c : V}
    (hsa : s ≠ a) (hsb : s ≠ b) (hsc : s ≠ c)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    {t delta lam : ℝ} {n : ℕ}
    (hn : 1 ≤ n)
    (hdelta0 : 0 ≤ delta)
    (hdeltaHalf : delta < (1 : ℝ) / 2)
    (ht : t = (n : ℝ) + delta)
    (hlam : lam = Real.pi / t)
    (Cs : CentreProjectiveCycle hp s)
    (Ca : CentreProjectiveCycle hp a)
    (Cb : CentreProjectiveCycle hp b)
    (Hs : HighExponentTransitionIntervalCertificate hp t s Cs)
    (Ha : HighExponentTransitionIntervalCertificate hp t a Ca)
    (Hb : HighExponentTransitionIntervalCertificate hp t b Cb)
    (hqsum : Hs.qe + Ha.qe + Hb.qe = 2 * n)
    (Cc : SupportIntervalCertificate (p := p) c)
    (hcturn : lam ≤ Cc.turnLength) :
    False := by
  have htpos :
      0 < t :=
    sendov_scale_pos hn hdelta0 ht
  have hlampos : 0 < lam := by
    rw [hlam]
    exact div_pos Real.pi_pos htpos
  have hsTurn :=
    SupportIntervalCertificate.qe_mul_lam_le_turnLength_ofHighExponent
      Hs htpos hlam
  have haTurn :=
    SupportIntervalCertificate.qe_mul_lam_le_turnLength_ofHighExponent
      Ha htpos hlam
  have hbTurn :=
    SupportIntervalCertificate.qe_mul_lam_le_turnLength_ofHighExponent
      Hb htpos hlam
  let Ss := SupportIntervalCertificate.ofHighExponent Hs
  let Sa := SupportIntervalCertificate.ofHighExponent Ha
  let Sb := SupportIntervalCertificate.ofHighExponent Hb
  have hpack :=
    SupportIntervalCertificate.four_turnLength_sum_le_two_pi
      hsa hsb hsc hab hac hbc Ss Sa Sb Cc
  have hqsumR :
      ((Hs.qe + Ha.qe + Hb.qe : ℕ) : ℝ) =
        ((2 * n : ℕ) : ℝ) := by
    exact_mod_cast hqsum
  have hhigh :
      ((2 * n : ℕ) : ℝ) * lam ≤
        Ss.turnLength + Sa.turnLength + Sb.turnLength := by
    dsimp [Ss, Sa, Sb]
    have hsTurn' := hsTurn
    have haTurn' := haTurn
    have hbTurn' := hbTurn
    rw [← hqsumR]
    push_cast
    nlinarith
  have htotal :
      (((2 * n + 1 : ℕ) : ℕ) : ℝ) * lam ≤
        Ss.turnLength + Sa.turnLength +
          Sb.turnLength + Cc.turnLength := by
    push_cast
    nlinarith
  have hpiBase : Real.pi = t * lam := by
    rw [hlam]
    field_simp [ne_of_gt htpos]
  have hpi :
      2 * Real.pi =
        2 * ((n : ℝ) + delta) * lam := by
    rw [hpiBase, ht]
  have hstrict :
      2 * ((n : ℝ) + delta) * lam <
        ((2 * n + 1 : ℕ) : ℝ) * lam := by
    push_cast
    nlinarith
  rw [hpi] at hpack
  nlinarith

/-- Specialized arithmetic form for the canonical mixed costs n,n-1,1. -/
theorem no_mixed_fourth_support_arc_of_canonical_costs
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane} {hp : Function.Injective p}
    {s a b c : V}
    (hsa : s ≠ a) (hsb : s ≠ b) (hsc : s ≠ c)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    {t delta lam : ℝ} {n : ℕ}
    (hn : 3 ≤ n)
    (hdelta0 : 0 ≤ delta)
    (hdeltaHalf : delta < (1 : ℝ) / 2)
    (ht : t = (n : ℝ) + delta)
    (hlam : lam = Real.pi / t)
    (Cs : CentreProjectiveCycle hp s)
    (Ca : CentreProjectiveCycle hp a)
    (Cb : CentreProjectiveCycle hp b)
    (Hs : HighExponentTransitionIntervalCertificate hp t s Cs)
    (Ha : HighExponentTransitionIntervalCertificate hp t a Ca)
    (Hb : HighExponentTransitionIntervalCertificate hp t b Cb)
    (hqs : Hs.qe = n)
    (hqa : Ha.qe = n - 1)
    (hqb : Hb.qe = 1)
    (Cc : SupportIntervalCertificate (p := p) c)
    (hcturn : lam ≤ Cc.turnLength) :
    False := by
  apply no_mixed_fourth_support_arc_of_one_cap_unit
    hsa hsb hsc hab hac hbc
    (by omega : 1 ≤ n)
    hdelta0 hdeltaHalf ht hlam
    Cs Ca Cb Hs Ha Hb
  · rw [hqs, hqa, hqb]
    omega
  · exact Cc
  · exact hcturn

#print axioms no_mixed_fourth_support_arc_of_one_cap_unit
#print axioms no_mixed_fourth_support_arc_of_canonical_costs

end JSP000404Research
