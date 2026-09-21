import JSP000404Research.TransitionCertificateFromDecomposition
import JSP000404Research.FourCentreTransitionCases
import Mathlib.Tactic

/-!
# The preserved mixed transition quotient is one

The mixed four-centre packing theorem already proves that the transition
quotient at the support-two centre is one, provided the transition is supplied
as a HighExponentTransitionIntervalCertificate.

TransitionCertificateFromDecomposition lets us start instead from the exact
ray/sign decomposition returned by
concrete_centre_large_exponent_has_positive_transition_gap.  Therefore the
quotient qe occurring in that preserved decomposition is exactly one.
-/

namespace JSP000404Research

theorem mixed_transition_decomposition_qe_eq_one
    {p : Fin 4 → Plane}
    (hp : Function.Injective p)
    (hcap : AngleCap p lam)
    {lam t delta : ℝ} {n : ℕ}
    (hn : 3 ≤ n)
    (hdelta0 : 0 ≤ delta)
    (hdeltaHalf : delta < (1 : ℝ) / 2)
    (ht : t = (n : ℝ) + delta)
    (hlam : lam = Real.pi / t)
    {s a b : Fin 4}
    (hsa : s ≠ a) (hsb : s ≠ b) (hab : a ≠ b)
    (Cs : CentreProjectiveCycle hp s)
    (Ca : CentreProjectiveCycle hp a)
    (Cb : CentreProjectiveCycle hp b)
    (hS : centreExponent Cs t = n - 1)
    (hA : centreExponent Ca t = n - 2)
    (hsupA : positiveSupport (centreQuotient Ca t) = 1)
    (first : OtherVertex b)
    (rest : List (OtherVertex b))
    (pre post : List ℕ)
    (qe : ℕ)
    (hrays : Cb.rays = first :: rest)
    (hqe : qe ≠ 0)
    (hq :
      quotientList t Cb.gaps =
        pre ++ qe :: post)
    (hsignLift :
      liftedCentreSignPath hp b first rest =
        List.replicate pre.length (raySignAt hp b first) ++
          List.replicate (post.length + 1)
            (!raySignAt hp b first)) :
    qe = 1 := by
  have hdelta1 : delta < 1 := by linarith
  have htpos :
      0 < t :=
    sendov_scale_pos (by omega : 1 ≤ n) hdelta0 ht
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
  obtain ⟨HB, hHB⟩ :=
    exists_highExponentTransitionIntervalCertificate_of_decomposition
      hp htpos b Cb first rest pre post qe
      hrays hqe hq hsignLift
  have hqB :
      HB.qe = 1 :=
    mixed_deficit_two_transition_qe_eq_one
      hp hn hdelta0 hdeltaHalf ht
      hsa hsb hab
      Cs Ca Cb HS HA HB
      hS hA hsupA
  rw [hHB] at hqB
  exact hqB

#print axioms mixed_transition_decomposition_qe_eq_one

end JSP000404Research
