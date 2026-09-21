import JSP000404Research.OneTransitionSupportInterval
import JSP000404Research.FinFourCentreCycle
import Mathlib.Tactic

/-!
# A strictly exposed four-point centre has one quantitative support transition

Around a centre of a four-point configuration there are exactly three
canonical projective rays.  If their lifted canonical signs changed three
times, the sorted signs would alternate

  sigma, !sigma, sigma.

Writing the sorted projective parameters as a <= b <= c, the sine
interpolation identity

  sin(c-b) d(a) + sin(b-a) d(c) = sin(c-a) d(b)

shows that, after the alternating sign reversal, the three actual unit rays
have a positive linear combination equal to zero.  This is incompatible with
one vector having strictly positive inner product with all three rays.

Hence a strictly exposed four-point centre has exactly one lifted sign
transition.  OneTransitionSupportInterval then converts that transition into
a common-signed support interval whose dual turn length is at least lambda.

This closes the quantitative geometric bridge needed by the mixed exterior
four-centre branch.
-/

namespace JSP000404Research

open Real

/-- Sine interpolation for three ordered planar unit directions.  The identity
itself is algebraic and does not require the ordering hypotheses. -/
theorem rayDirection_sine_interpolation
    (a b c : ℝ) :
    Real.sin (c - b) • rayDirection a +
        Real.sin (b - a) • rayDirection c =
      Real.sin (c - a) • rayDirection b := by
  ext k
  fin_cases k <;>
    simp [rayDirection, Real.sin_sub] <;>
    ring

/-- With alternating projective signs, the same sine coefficients give a
linear dependence of the three actual unit rays. -/
theorem alternating_signedRay_sine_combo
    (sigma : Bool) (a b c : ℝ) :
    Real.sin (c - b) • signedRayDirection sigma a +
        Real.sin (c - a) • signedRayDirection (!sigma) b +
        Real.sin (b - a) • signedRayDirection sigma c =
      0 := by
  cases sigma <;>
  ext k
  fin_cases k <;>
    simp [signedRayDirection, rayDirection, Real.sin_sub] <;>
    ring

/-- Strict support of an actual displacement implies strict support of its
unit signed-ray factor because the canonical radius is positive. -/
theorem inner_signedRay_pos_of_strictSupportsAt
    {V : Type*} {p : V → Plane}
    (hp : Function.Injective p)
    {i : V} {u : Plane}
    (hu : StrictSupportsAt p i u)
    (j : OtherVertex i) :
    0 <
      inner ℝ u
        (signedRayDirection
          (raySignAt hp i j)
          (rayThetaAt hp i j)) := by
  have h := hu j.1 j.2
  rw [rayRepAt_eq hp i j, inner_smul_right] at h
  have hrho := rayRhoAt_pos hp i j
  rcases (mul_pos_iff.mp h) with hpos | hneg
  · exact hpos.2
  · exact False.elim ((not_lt_of_ge hrho.le) hneg.1)

/-- Three sorted canonical rays with alternating signs cannot share one strict
supporting vector. -/
theorem no_strictSupport_of_three_alternating_sorted
    {V : Type*} {p : V → Plane}
    (hp : Function.Injective p)
    {i : V}
    (r0 r1 r2 : OtherVertex i)
    (h01 :
      rayThetaAt hp i r0 ≤ rayThetaAt hp i r1)
    (h12 :
      rayThetaAt hp i r1 ≤ rayThetaAt hp i r2)
    (hs1 :
      raySignAt hp i r1 = !raySignAt hp i r0)
    (hs2 :
      raySignAt hp i r2 = raySignAt hp i r0)
    (u : Plane)
    (hu : StrictSupportsAt p i u) :
    False := by
  have hu0 :=
    inner_signedRay_pos_of_strictSupportsAt hp hu r0
  have hu1 :=
    inner_signedRay_pos_of_strictSupportsAt hp hu r1
  have hu2 :=
    inner_signedRay_pos_of_strictSupportsAt hp hu r2
  by_cases h01eq :
      rayThetaAt hp i r0 = rayThetaAt hp i r1
  · have hneg :
        signedRayDirection
            (raySignAt hp i r1)
            (rayThetaAt hp i r1)
          =
        - signedRayDirection
            (raySignAt hp i r0)
            (rayThetaAt hp i r0) := by
      rw [hs1, ← h01eq]
      exact signedRayDirection_not_eq_neg
        (raySignAt hp i r0) (rayThetaAt hp i r0)
    rw [hneg, inner_neg_right] at hu1
    linarith
  by_cases h12eq :
      rayThetaAt hp i r1 = rayThetaAt hp i r2
  · have hneg :
        signedRayDirection
            (raySignAt hp i r1)
            (rayThetaAt hp i r1)
          =
        - signedRayDirection
            (raySignAt hp i r2)
            (rayThetaAt hp i r2) := by
      rw [hs1, hs2, h12eq]
      simpa using
        (signedRayDirection_not_eq_neg
          (raySignAt hp i r0) (rayThetaAt hp i r2))
    rw [hneg, inner_neg_right] at hu1
    linarith
  have h01lt :
      rayThetaAt hp i r0 < rayThetaAt hp i r1 :=
    lt_of_le_of_ne h01 h01eq
  have h12lt :
      rayThetaAt hp i r1 < rayThetaAt hp i r2 :=
    lt_of_le_of_ne h12 h12eq
  have hA :
      0 <
        Real.sin
          (rayThetaAt hp i r2 - rayThetaAt hp i r1) := by
    apply Real.sin_pos_of_pos_of_lt_pi
    · linarith
    · have h2pi := rayThetaAt_lt_pi hp i r2
      have h10 := rayThetaAt_nonneg hp i r1
      linarith
  have hB :
      0 <
        Real.sin
          (rayThetaAt hp i r1 - rayThetaAt hp i r0) := by
    apply Real.sin_pos_of_pos_of_lt_pi
    · linarith
    · have h1pi := rayThetaAt_lt_pi hp i r1
      have h00 := rayThetaAt_nonneg hp i r0
      linarith
  have hC :
      0 <
        Real.sin
          (rayThetaAt hp i r2 - rayThetaAt hp i r0) := by
    apply Real.sin_pos_of_pos_of_lt_pi
    · linarith
    · have h2pi := rayThetaAt_lt_pi hp i r2
      have h00 := rayThetaAt_nonneg hp i r0
      linarith
  rw [hs1] at hu1
  rw [hs2] at hu2
  have hvec :=
    alternating_signedRay_sine_combo
      (raySignAt hp i r0)
      (rayThetaAt hp i r0)
      (rayThetaAt hp i r1)
      (rayThetaAt hp i r2)
  have hinner :=
    congrArg (fun x : Plane => inner ℝ u x) hvec
  simp only [inner_add_right, inner_smul_right, inner_zero_right] at hinner
  have hterm0 :
      0 <
        Real.sin (rayThetaAt hp i r2 - rayThetaAt hp i r1) *
          inner ℝ u
            (signedRayDirection
              (raySignAt hp i r0)
              (rayThetaAt hp i r0)) :=
    mul_pos hA hu0
  have hterm1 :
      0 <
        Real.sin (rayThetaAt hp i r2 - rayThetaAt hp i r0) *
          inner ℝ u
            (signedRayDirection
              (!raySignAt hp i r0)
              (rayThetaAt hp i r1)) :=
    mul_pos hC hu1
  have hterm2 :
      0 <
        Real.sin (rayThetaAt hp i r1 - rayThetaAt hp i r0) *
          inner ℝ u
            (signedRayDirection
              (raySignAt hp i r0)
              (rayThetaAt hp i r2)) :=
    mul_pos hB hu2
  linarith

/-- For three Boolean rays, the antiperiodic lifted path has either one or
three transitions. -/
theorem lifted_three_transition_count_one_or_three
    (s0 s1 s2 : Bool) :
    boolTransitionCountFrom s0 [s1, s2, !s0] = 1 ∨
      boolTransitionCountFrom s0 [s1, s2, !s0] = 3 := by
  cases s0 <;> cases s1 <;> cases s2 <;>
    simp [boolTransitionCountFrom]

/-- Three transitions force the alternating sign pattern. -/
theorem lifted_three_transition_count_three_shape
    (s0 s1 s2 : Bool)
    (h :
      boolTransitionCountFrom s0 [s1, s2, !s0] = 3) :
    s1 = !s0 ∧ s2 = s0 := by
  cases s0 <;> cases s1 <;> cases s2 <;>
    simp [boolTransitionCountFrom] at h ⊢

/-- Strict exposure removes the three-transition alternative, so the concrete
four-point lifted sign path changes exactly once. -/
theorem one_sign_transition_of_strictlyExposed_fin_four
    {p : Fin 4 → Plane}
    (hp : Function.Injective p)
    {i : Fin 4}
    (C : CentreProjectiveCycle hp i)
    (hExpose : StrictlyExposedAt p i) :
    ∃ first : OtherVertex i, ∃ rest : List (OtherVertex i),
      C.rays = first :: rest ∧
      boolTransitionCountFrom
          (raySignAt hp i first)
          (liftedCentreSignPath hp i first rest) = 1 := by
  obtain ⟨r0, r1, r2, hrays⟩ :=
    exists_three_rays_of_fin4_cycle i C
  have hord :=
    three_ray_theta_order C r0 r1 r2 hrays
  have hcases :=
    lifted_three_transition_count_one_or_three
      (raySignAt hp i r0)
      (raySignAt hp i r1)
      (raySignAt hp i r2)
  have hne3 :
      boolTransitionCountFrom
          (raySignAt hp i r0)
          [raySignAt hp i r1,
           raySignAt hp i r2,
           !raySignAt hp i r0] ≠ 3 := by
    intro hthree
    have hshape :=
      lifted_three_transition_count_three_shape
        (raySignAt hp i r0)
        (raySignAt hp i r1)
        (raySignAt hp i r2)
        hthree
    obtain ⟨u, hu⟩ := hExpose
    exact no_strictSupport_of_three_alternating_sorted
      hp r0 r1 r2 hord.1 hord.2
      hshape.1 hshape.2 u hu
  have hone :
      boolTransitionCountFrom
          (raySignAt hp i r0)
          [raySignAt hp i r1,
           raySignAt hp i r2,
           !raySignAt hp i r0] = 1 :=
    hcases.resolve_right hne3
  refine ⟨r0, [r1, r2], ?_, ?_⟩
  · exact hrays
  · simpa [liftedCentreSignPath] using hone

/-- Quantitative form: every strictly exposed centre of a four-point
configuration owns a support interval of turn at least lambda. -/
theorem exists_supportIntervalCertificate_of_strictlyExposed_fin_four
    {p : Fin 4 → Plane}
    (hp : Function.Injective p)
    (hcap : AngleCap p lam)
    {lam t : ℝ}
    (ht : 0 < t)
    (htone : 1 ≤ t)
    (hlam : lam = Real.pi / t)
    {i : Fin 4}
    (C : CentreProjectiveCycle hp i)
    (hExpose : StrictlyExposedAt p i) :
    ∃ S : SupportIntervalCertificate (p := p) i,
      lam ≤ S.turnLength := by
  obtain ⟨first, rest, hrays, htrans⟩ :=
    one_sign_transition_of_strictlyExposed_fin_four
      hp C hExpose
  exact exists_supportIntervalCertificate_of_one_sign_transition
    hp hcap ht htone hlam i C first rest hrays htrans

#print axioms rayDirection_sine_interpolation
#print axioms alternating_signedRay_sine_combo
#print axioms no_strictSupport_of_three_alternating_sorted
#print axioms one_sign_transition_of_strictlyExposed_fin_four
#print axioms exists_supportIntervalCertificate_of_strictlyExposed_fin_four

end JSP000404Research
