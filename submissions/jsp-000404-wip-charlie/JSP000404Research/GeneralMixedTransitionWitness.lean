import JSP000404Research.TransitionCertificateFromDecomposition
import JSP000404Research.FourCentreTransitionCases
import Mathlib.Tactic

/-!
# The genuine mixed transition quotient equals one at arbitrary finite cardinality

The Fin 4 argument does not require four rays: the three-centre transition
packing theorem already works for any finite ordered vertex set.  This
theorem preserves the exact ray/sign quotient decomposition at centre b,
reconstructs its original transition certificate, and proves that the
distinguished quotient is one from authentic sharp/support-one data.
-/

namespace JSP000404Research

theorem general_mixed_transition_decomposition_qe_eq_one
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
    {s a b : V}
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
    (hq : quotientList t Cb.gaps = pre ++ qe :: post)
    (hsignLift :
      liftedCentreSignPath hp b first rest =
        List.replicate pre.length (raySignAt hp b first) ++
          List.replicate (post.length + 1)
            (!raySignAt hp b first)) :
    qe = 1 := by
  have hdelta1 : delta < 1 := by linarith
  have htpos : 0 < t :=
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
        a Ca (by rw [hA]))
  obtain ⟨HB, hHB⟩ :=
    exists_highExponentTransitionIntervalCertificate_of_decomposition
      hp htpos b Cb first rest pre post qe
      hrays hqe hq hsignLift
  have hqB : HB.qe = 1 :=
    mixed_deficit_two_transition_qe_eq_one
      hp hn hdelta0 hdeltaHalf ht
      hsa hsb hab
      Cs Ca Cb HS HA HB
      hS hA hsupA
  rw [hHB] at hqB
  exact hqB

#print axioms general_mixed_transition_decomposition_qe_eq_one

end JSP000404Research
