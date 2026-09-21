import JSP000404Research.ThreeStepTransitionShape
import JSP000404Research.FourCentreSupportTwoSmallAngle
import JSP000404Research.LinearizedTransitionExposure
import Mathlib.Tactic

/-!
# A non-transition quotient in a three-ray cycle pays a genuine angle

For a four-point centre there are three projective gaps.  Suppose an exact
transition decomposition marks one distinguished quotient qe and its lifted
sign blocks.  Any different quotient value occurring in the three-gap list is
therefore carried by a no-transition gap.

On an ordinary no-transition gap the two canonical signs agree, so the genuine
Euclidean angle equals the physical projective gap.  On the wrap no-transition
gap the last sign equals the lifted first sign, and the same equality holds.

Thus every quotient q != qe occurring in the three-gap list pays a genuine
angle of at least q*lambda.
-/

namespace JSP000404Research

open Real

theorem exists_actual_angle_paying_nontransition_quotient_fin_four
    {p : Fin 4 → Plane}
    (hp : Function.Injective p)
    {t lam : ℝ}
    (ht : 0 < t)
    (hlam : lam = Real.pi / t)
    (i : Fin 4)
    (C : CentreProjectiveCycle hp i)
    (r0 r1 r2 : OtherVertex i)
    (hrays : C.rays = [r0,r1,r2])
    (pre post : List ℕ)
    (qe q : ℕ)
    (hqeDecomp :
      quotientList t C.gaps = pre ++ qe :: post)
    (hsignLift :
      liftedCentreSignPath hp i r0 [r1,r2] =
        List.replicate pre.length (raySignAt hp i r0) ++
          List.replicate (post.length + 1)
            (!raySignAt hp i r0))
    (hqne : q ≠ qe)
    (hqmem : q ∈ quotientList t C.gaps) :
    ∃ x y : OtherVertex i,
      x ≠ y ∧
      (q : ℝ) * lam ≤
        EuclideanGeometry.angle (p x.1) (p i) (p y.1) := by
  let g0 :=
    (rayThetaAt hp i r1 - rayThetaAt hp i r0) / Real.pi
  let g1 :=
    (rayThetaAt hp i r2 - rayThetaAt hp i r1) / Real.pi
  let g2 :=
    (rayThetaAt hp i r0 + Real.pi -
      rayThetaAt hp i r2) / Real.pi
  let q0 := Nat.floor (t * g0)
  let q1 := Nat.floor (t * g1)
  let q2 := Nat.floor (t * g2)
  have hgaps : C.gaps = [g0,g1,g2] := by
    simpa [g0, g1, g2] using
      centre_gaps_eq_three_rays i C r0 r1 r2 hrays
  have hqlist :
      quotientList t C.gaps = [q0,q1,q2] := by
    rw [hgaps]
    simp [quotientList, q0, q1, q2]
  have hthreeQ :
      [q0,q1,q2] = pre ++ qe :: post := by
    rw [← hqlist]
    exact hqeDecomp
  have hthreeSign :
      [raySignAt hp i r1,
       raySignAt hp i r2,
       !raySignAt hp i r0] =
        List.replicate pre.length (raySignAt hp i r0) ++
          List.replicate (post.length + 1)
            (!raySignAt hp i r0) := by
    simpa [liftedCentreSignPath] using hsignLift
  have hshape :=
    three_step_same_sign_of_ne_transition_value
      (raySignAt hp i r0)
      (raySignAt hp i r1)
      (raySignAt hp i r2)
      q0 q1 q2 qe pre post hthreeQ hthreeSign
  have halign0 :=
    centreQuotient_aligned C ht.le
  have halign :
      (q0 : ℝ) ≤ t * g0 ∧
      (q1 : ℝ) ≤ t * g1 ∧
      (q2 : ℝ) ≤ t * g2 := by
    simpa [QuotientGapAligned, hqlist, hgaps] using halign0
  have hpair :
      [r0,r1,r2].Pairwise
        (fun a b =>
          rayThetaAt hp i a ≤ rayThetaAt hp i b) := by
    rw [← hrays]
    exact C.theta_sorted
  have horder01 :
      rayThetaAt hp i r0 ≤ rayThetaAt hp i r1 :=
    (List.pairwise_cons.mp hpair).1 r1 (by simp)
  have horder12 :
      rayThetaAt hp i r1 ≤ rayThetaAt hp i r2 :=
    (List.pairwise_cons.mp
      (List.pairwise_cons.mp hpair).2).1 r2 (by simp)
  have horder02 :
      rayThetaAt hp i r0 ≤ rayThetaAt hp i r2 :=
    (List.pairwise_cons.mp hpair).1 r2 (by simp)
  have hnod :
      r0 ≠ r1 ∧ r0 ≠ r2 ∧ r1 ≠ r2 := by
    have h := C.nodup
    rw [hrays] at h
    simpa using h
  rw [hqlist] at hqmem
  simp only [List.mem_cons, List.mem_singleton] at hqmem
  rcases hqmem with hq0 | hq1 | hq2
  · have hq0ne : q0 ≠ qe := by
      intro h
      apply hqne
      rw [hq0, h]
    have hs01 :
        raySignAt hp i r0 = raySignAt hp i r1 :=
      (hshape.1 hq0ne).symm
    have hang :=
      actual_angle_eq_ordinary_projective_gap_of_sign_eq
        hp i horder01 hs01
    have hpay :=
      quotient_mul_lam_le_pi_mul_gap
        ht halign.1 hlam
    refine ⟨r0, r1, hnod.1, ?_⟩
    rw [hq0]
    calc
      (q0 : ℝ) * lam ≤ Real.pi * g0 := hpay
      _ = rayThetaAt hp i r1 - rayThetaAt hp i r0 := by
        dsimp [g0]
        field_simp [Real.pi_ne_zero]
      _ = EuclideanGeometry.angle (p r0.1) (p i) (p r1.1) :=
        hang.symm
  · have hq1ne : q1 ≠ qe := by
      intro h
      apply hqne
      rw [hq1, h]
    have hs12 :
        raySignAt hp i r1 = raySignAt hp i r2 :=
      (hshape.2.1 hq1ne).symm
    have hang :=
      actual_angle_eq_ordinary_projective_gap_of_sign_eq
        hp i horder12 hs12
    have hpay :=
      quotient_mul_lam_le_pi_mul_gap
        ht halign.2.1 hlam
    refine ⟨r1, r2, hnod.2.2, ?_⟩
    rw [hq1]
    calc
      (q1 : ℝ) * lam ≤ Real.pi * g1 := hpay
      _ = rayThetaAt hp i r2 - rayThetaAt hp i r1 := by
        dsimp [g1]
        field_simp [Real.pi_ne_zero]
      _ = EuclideanGeometry.angle (p r1.1) (p i) (p r2.1) :=
        hang.symm
  · have hq2ne : q2 ≠ qe := by
      intro h
      apply hqne
      rw [hq2, h]
    have hs20 :
        raySignAt hp i r2 = !raySignAt hp i r0 :=
      hshape.2.2 hq2ne
    have hang :=
      actual_angle_eq_wrap_projective_gap_of_lifted_sign_eq
        hp i horder02 hs20
    have hpay :=
      quotient_mul_lam_le_pi_mul_gap
        ht halign.2.2 hlam
    refine ⟨r2, r0, hnod.2.1.symm, ?_⟩
    rw [hq2]
    calc
      (q2 : ℝ) * lam ≤ Real.pi * g2 := hpay
      _ =
          rayThetaAt hp i r0 + Real.pi -
            rayThetaAt hp i r2 := by
        dsimp [g2]
        field_simp [Real.pi_ne_zero]
      _ = EuclideanGeometry.angle (p r2.1) (p i) (p r0.1) :=
        hang.symm

#print axioms exists_actual_angle_paying_nontransition_quotient_fin_four

end JSP000404Research
