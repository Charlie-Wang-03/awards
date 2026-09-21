import JSP000404Research.FourPointConvexSeparation
import JSP000404Research.ExposedSupportIntervalFinFour
import JSP000404Research.FourCentreMixedExteriorOutlet
import JSP000404Research.FourCentreTransitionCases
import Mathlib.Tactic

/-!
# The mixed four-centre exterior branch is impossible

Assume the canonical mixed sharp-layer pattern

  exponent(s) = n-1,
  exponent(a) = n-2 with quotient support one,
  exponent(b) = n-2 with quotient support two.

Transition packing gives the three high-transition costs

  n, n-1, 1.

If the fourth point c lies outside the triangle of s,a,b, Hahn--Banach exposes
c strictly.  ExposedSupportIntervalFinFour upgrades this to a genuine support
interval of turn at least lambda.  The four disjoint support arcs then exceed
the full 2*pi direction circle because delta<1/2.

Thus the mixed branch cannot be exterior; any surviving mixed configuration
must put the fourth point in the convex hull of the three high-exponent
centres.
-/

namespace JSP000404Research

open Real

theorem no_mixed_fourth_outside_triangle_fin_four
    {p : Fin 4 → Plane}
    (hp : Function.Injective p)
    (hcap : AngleCap p lam)
    {lam t delta : ℝ} {n : ℕ}
    (hn : 3 ≤ n)
    (hdelta0 : 0 ≤ delta)
    (hdeltaHalf : delta < (1 : ℝ) / 2)
    (ht : t = (n : ℝ) + delta)
    (hlam : lam = Real.pi / t)
    {s a b c : Fin 4}
    (hsa : s ≠ a) (hsb : s ≠ b) (hsc : s ≠ c)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (Cs : CentreProjectiveCycle hp s)
    (Ca : CentreProjectiveCycle hp a)
    (Cb : CentreProjectiveCycle hp b)
    (hS : centreExponent Cs t = n - 1)
    (hA : centreExponent Ca t = n - 2)
    (hB : centreExponent Cb t = n - 2)
    (hsupA : positiveSupport (centreQuotient Ca t) = 1)
    (hsupB : positiveSupport (centreQuotient Cb t) = 2)
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
  let Hs :=
    Classical.choice
      (exists_highExponentTransitionIntervalCertificate
        hp hcap (by omega : 1 ≤ n)
        hdelta0 hdelta1 ht hlam
        s Cs (by rw [hS]; omega))
  let Ha :=
    Classical.choice
      (exists_highExponentTransitionIntervalCertificate
        hp hcap (by omega : 1 ≤ n)
        hdelta0 hdelta1 ht hlam
        a Ca (by rw [hA]; omega))
  let Hb :=
    Classical.choice
      (exists_highExponentTransitionIntervalCertificate
        hp hcap (by omega : 1 ≤ n)
        hdelta0 hdelta1 ht hlam
        b Cb (by rw [hB]; omega))
  have hqs : Hs.qe = n := by
    exact unit_deficit_transition_qe_eq_n
      Cs Hs (by omega) hdelta0 hdelta1 ht hS
  have hqa : Ha.qe = n - 1 := by
    exact deficit_two_support_one_transition_qe_eq
      Ca Ha hn hA hsupA
  have hqb : Hb.qe = 1 := by
    exact mixed_deficit_two_transition_qe_eq_one
      hp hn hdelta0 hdeltaHalf ht
      hsa hsb hab
      Cs Ca Cb Hs Ha Hb
      hS hA hsupA
  have hExpose :
      StrictlyExposedAt p c :=
    strictlyExposedAt_of_not_mem_other_triangle_fin_four
      hp hsa hsb hsc hab hac hbc hout
  have hother : Nonempty (OtherVertex c) :=
    ⟨⟨s, hsc⟩⟩
  let Cc : CentreProjectiveCycle hp c :=
    Classical.choice (exists_centreProjectiveCycle hp c hother)
  obtain ⟨Sc, hSc⟩ :=
    exists_supportIntervalCertificate_of_strictlyExposed_fin_four
      hp hcap htpos htone hlam Cc hExpose
  exact no_mixed_fourth_support_arc_of_canonical_costs
    hsa hsb hsc hab hac hbc
    hn hdelta0 hdeltaHalf ht hlam
    Cs Ca Cb Hs Ha Hb
    hqs hqa hqb Sc hSc

#print axioms no_mixed_fourth_outside_triangle_fin_four

end JSP000404Research
