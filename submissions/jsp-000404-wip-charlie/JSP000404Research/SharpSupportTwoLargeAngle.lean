import JSP000404Research.SharpPinnedSupportTwoCluster
import JSP000404Research.HiddenLargeAngleTriangle
import Mathlib.Geometry.Euclidean.Angle.Unoriented.TriangleInequality
import Mathlib.Tactic

/-!
# A unit-transition support-two centre sees the sharp ray at a huge angle

Let s be a sharp centre and i a deficit-two/support-two centre.  Suppose the
unique sign-transition quotient at i is one.

The hidden same-sign quotient is n-1 and therefore pays a genuine angle of at
least (n-1)*lambda.  SharpPinnedSupportTwoCluster says every angle at i whose
two endpoint rays both avoid s is at most delta*lambda.  Since n>=3 and
delta<1/2, the hidden large angle must therefore contain the ray to s.

Consequently every other non-sharp ray a satisfies

  ((n-1)-delta)*lambda <= angle(s,i,a),

by the angle triangle inequality and the delta*lambda diameter of the
non-sharp cluster.
-/

namespace JSP000404Research

open Real

theorem sharp_supportTwo_unit_transition_hidden_contains_sharp
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
    {s i : V}
    (hsi : s ≠ i)
    (hs : SharpAt p delta lam s)
    (C : CentreProjectiveCycle hp i)
    (hexp : centreExponent C t = n - 2)
    (hsupport :
      positiveSupport (centreQuotient C t) = 2)
    (first : OtherVertex i)
    (rest : List (OtherVertex i))
    (pre post : List ℕ)
    (qe : ℕ)
    (hrays : C.rays = first :: rest)
    (hqe0 : qe ≠ 0)
    (hq :
      quotientList t C.gaps =
        pre ++ qe :: post)
    (hsignLift :
      liftedCentreSignPath hp i first rest =
        List.replicate pre.length (raySignAt hp i first) ++
          List.replicate (post.length + 1)
            (!raySignAt hp i first))
    (hqeOne : qe = 1) :
    ∃ x y : OtherVertex i,
      x ≠ y ∧
      (x.1 = s ∨ y.1 = s) ∧
      (((n - 1 : ℕ) : ℝ) * lam) ≤
        EuclideanGeometry.angle (p x.1) (p i) (p y.1) := by
  obtain ⟨x, y, hxy, hlarge⟩ :=
    support_two_unit_transition_hidden_angle
      hp hcap hn hdelta0 hdeltaHalf ht hlam
      i C hexp hsupport
      first rest pre post qe
      hrays hqe0 hq hsignLift hqeOne
  have hcluster :
      OuterSmallAwayFrom p delta lam s i :=
    supportTwo_outerSmallAwayFrom_sharp
      hp hcap hn hdelta0 hdeltaHalf ht hlam
      hsi hs C hexp hsupport
  have htpos :
      0 < t :=
    sendov_scale_pos (by omega : 1 ≤ n) hdelta0 ht
  have hlampos : 0 < lam := by
    rw [hlam]
    exact div_pos Real.pi_pos htpos
  have hcontains : x.1 = s ∨ y.1 = s := by
    by_contra hnone
    have hxS : x.1 ≠ s := by
      intro h
      exact hnone (Or.inl h)
    have hyS : y.1 ≠ s := by
      intro h
      exact hnone (Or.inr h)
    have hsmall :
        EuclideanGeometry.angle
            (p x.1) (p i) (p y.1)
          ≤ delta * lam :=
      hcluster x.1 y.1 x.2 y.2
        hxS hyS (otherVertex_val_ne hxy)
    have hcoef :
        delta * lam <
          (((n - 1 : ℕ) : ℝ) * lam) := by
      have hnsub : (1 : ℝ) < ((n - 1 : ℕ) : ℝ) := by
        exact_mod_cast (by omega : 1 < n - 1)
      nlinarith
    linarith
  exact ⟨x, y, hxy, hcontains, hlarge⟩

/-- Quantitative corollary: every non-sharp ray is separated from the sharp ray
by at least ((n-1)-delta)*lambda at the support-two centre. -/
theorem sharp_supportTwo_unit_transition_angle_lower
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
    {s i a : V}
    (hsi : s ≠ i)
    (hai : a ≠ i)
    (has : a ≠ s)
    (hs : SharpAt p delta lam s)
    (C : CentreProjectiveCycle hp i)
    (hexp : centreExponent C t = n - 2)
    (hsupport :
      positiveSupport (centreQuotient C t) = 2)
    (first : OtherVertex i)
    (rest : List (OtherVertex i))
    (pre post : List ℕ)
    (qe : ℕ)
    (hrays : C.rays = first :: rest)
    (hqe0 : qe ≠ 0)
    (hq :
      quotientList t C.gaps =
        pre ++ qe :: post)
    (hsignLift :
      liftedCentreSignPath hp i first rest =
        List.replicate pre.length (raySignAt hp i first) ++
          List.replicate (post.length + 1)
            (!raySignAt hp i first))
    (hqeOne : qe = 1) :
    (((n - 1 : ℕ) : ℝ) - delta) * lam ≤
      EuclideanGeometry.angle (p s) (p i) (p a) := by
  obtain ⟨x, y, hxy, hcontains, hlarge⟩ :=
    sharp_supportTwo_unit_transition_hidden_contains_sharp
      hp hcap hn hdelta0 hdeltaHalf ht hlam
      hsi hs C hexp hsupport
      first rest pre post qe
      hrays hqe0 hq hsignLift hqeOne
  have hcluster :
      OuterSmallAwayFrom p delta lam s i :=
    supportTwo_outerSmallAwayFrom_sharp
      hp hcap hn hdelta0 hdeltaHalf ht hlam
      hsi hs C hexp hsupport
  have htpos :
      0 < t :=
    sendov_scale_pos (by omega : 1 ≤ n) hdelta0 ht
  have hlampos : 0 < lam := by
    rw [hlam]
    exact div_pos Real.pi_pos htpos
  rcases hcontains with hxS | hyS
  · have hlargeS :
        (((n - 1 : ℕ) : ℝ) * lam) ≤
          EuclideanGeometry.angle (p s) (p i) (p y.1) := by
      simpa [hxS] using hlarge
    have hyNotS : y.1 ≠ s := by
      intro hyS
      apply hxy
      apply Subtype.ext
      exact hxS.trans hyS.symm
    by_cases hay : a = y.1
    · rw [hay]
      nlinarith
    · have hsmall :
          EuclideanGeometry.angle (p a) (p i) (p y.1) ≤
            delta * lam :=
        hcluster a y.1 hai y.2 has hyNotS hay
      have htri :
          EuclideanGeometry.angle (p s) (p i) (p y.1) ≤
            EuclideanGeometry.angle (p s) (p i) (p a) +
              EuclideanGeometry.angle (p a) (p i) (p y.1) := by
        change
          InnerProductGeometry.angle
              (p s - p i) (p y.1 - p i) ≤
            InnerProductGeometry.angle
              (p s - p i) (p a - p i) +
            InnerProductGeometry.angle
              (p a - p i) (p y.1 - p i)
        exact InnerProductGeometry.angle_le_angle_add_angle _ _ _
      nlinarith
  · have hlargeS :
        (((n - 1 : ℕ) : ℝ) * lam) ≤
          EuclideanGeometry.angle (p s) (p i) (p x.1) := by
      have hcomm :
          EuclideanGeometry.angle (p x.1) (p i) (p s) =
            EuclideanGeometry.angle (p s) (p i) (p x.1) :=
        EuclideanGeometry.angle_comm _ _ _
      rw [hyS, hcomm] at hlarge
      exact hlarge
    have hxNotS : x.1 ≠ s := by
      intro hxS
      apply hxy
      apply Subtype.ext
      exact hxS.trans hyS.symm
    by_cases hax : a = x.1
    · rw [hax]
      nlinarith
    · have hsmall :
          EuclideanGeometry.angle (p a) (p i) (p x.1) ≤
            delta * lam :=
        hcluster a x.1 hai x.2 has hxNotS hax
      have htri :
          EuclideanGeometry.angle (p s) (p i) (p x.1) ≤
            EuclideanGeometry.angle (p s) (p i) (p a) +
              EuclideanGeometry.angle (p a) (p i) (p x.1) := by
        change
          InnerProductGeometry.angle
              (p s - p i) (p x.1 - p i) ≤
            InnerProductGeometry.angle
              (p s - p i) (p a - p i) +
            InnerProductGeometry.angle
              (p a - p i) (p x.1 - p i)
        exact InnerProductGeometry.angle_le_angle_add_angle _ _ _
      nlinarith

#print axioms sharp_supportTwo_unit_transition_hidden_contains_sharp
#print axioms sharp_supportTwo_unit_transition_angle_lower

end JSP000404Research
