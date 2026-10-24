import JSP000404Research.SeparatedSupportTwoSmallPair
import JSP000404Research.SharpOuterAngles
import Mathlib.Tactic

/-!
# Propagation of an actual small angle to both opposite triangle angles

Under the original planar AngleCap p lam, a small angle at a single
centre is enough to force large angles at the two other original
centres. SharpAt is NOT assumed for the source centre.

Applied to the kernel-certified separated support-two small-pair witness,
this produces two genuinely distinct non-top endpoints with angles
STRICTLY above delta*lam for every 0 <= delta < 1/2.

This is a local original-plane triangle constraint, NOT a global
non-reusing TRUE-hole/dyadic payment.
-/

namespace JSP000404Research

open Real

/-- A single actual angle of size at most delta*lam (not a global
SharpAt hypothesis) forces the opposite angle to be at least
(1-delta)*lam, by the planar angle-sum identity and AngleCap. -/
theorem outer_angle_ge_of_actual_small_angle
    {V : Type*} {p : V → Plane}
    {delta lam : ℝ}
    (hp : Function.Injective p)
    (hcap : AngleCap p lam)
    {s a b : V}
    (hsa : s ≠ a) (hsb : s ≠ b) (hab : a ≠ b)
    (hsmall :
      EuclideanGeometry.angle (p a) (p s) (p b) ≤ delta * lam) :
    (1 - delta) * lam ≤
      EuclideanGeometry.angle (p s) (p a) (p b) := by
  have hcapB :
      EuclideanGeometry.angle (p s) (p b) (p a) ≤
        Real.pi - lam :=
    hcap s b a hsb hsa hab.symm
  have hsum :
      EuclideanGeometry.angle (p a) (p s) (p b) +
      EuclideanGeometry.angle (p s) (p b) (p a) +
      EuclideanGeometry.angle (p b) (p a) (p s) =
        Real.pi := by
    simpa [add_assoc, add_left_comm, add_comm] using
      (EuclideanGeometry.angle_add_angle_add_angle_eq_pi
        (p₁ := p a) (p₂ := p s) (p b)
        (hp.ne hsa))
  have hcomm :
      EuclideanGeometry.angle (p b) (p a) (p s) =
        EuclideanGeometry.angle (p s) (p a) (p b) :=
    EuclideanGeometry.angle_comm _ _ _
  rw [hcomm] at hsum
  linarith

/-- A short angle at s makes both other angles large, using the
actual triangle rather than an all-pairs SharpAt certificate. -/
theorem both_outer_angles_ge_of_actual_small_angle
    {V : Type*} {p : V → Plane}
    {delta lam : ℝ}
    (hp : Function.Injective p)
    (hcap : AngleCap p lam)
    {s a b : V}
    (hsa : s ≠ a) (hsb : s ≠ b) (hab : a ≠ b)
    (hsmall :
      EuclideanGeometry.angle (p a) (p s) (p b) ≤ delta * lam) :
    (1 - delta) * lam ≤
        EuclideanGeometry.angle (p s) (p a) (p b) ∧
      (1 - delta) * lam ≤
        EuclideanGeometry.angle (p s) (p b) (p a) := by
  constructor
  · exact outer_angle_ge_of_actual_small_angle
      hp hcap hsa hsb hab hsmall
  · apply outer_angle_ge_of_actual_small_angle
      hp hcap hsb hsa hab.symm
    have hcomm :
        EuclideanGeometry.angle (p b) (p s) (p a) =
          EuclideanGeometry.angle (p a) (p s) (p b) :=
      EuclideanGeometry.angle_comm _ _ _
    rw [hcomm]
    exact hsmall

/-- A separated support-two minimum produces an actual non-top
triangle whose vertex angle at the minimum is small but BOTH
opposite vertex angles are strictly larger than delta*lam. -/
theorem separated_support_two_has_non_top_triangle_two_large_angles
    {V : Type*} [LinearOrder V] [Fintype V] [DecidableEq V]
    {p : V → Plane} (hp : Function.Injective p)
    {lam t delta : ℝ} {n : ℕ}
    (hcap : AngleCap p lam)
    (Cfam : ∀ v : V, CentreProjectiveCycle hp v)
    (hcard : Fintype.card V = 6)
    (hn : 5 ≤ n)
    (hdelta0 : 0 ≤ delta)
    (hdeltaHalf : delta < (1 : ℝ) / 2)
    (ht : t = (n : ℝ) + delta)
    (hlam : lam = Real.pi / t)
    (top : V)
    (hTop : centreExponent (Cfam top) t = n - 1)
    {i : V}
    (hit : i ≠ top)
    (hI : centreExponent (Cfam i) t = n - 3)
    (hsupport :
      positiveSupport (centreQuotient (Cfam i) t) = 2)
    (hsep : ¬ TopPinnedPositivePair Cfam top i hit t) :
    ∃ x y : OtherVertex i,
      x ≠ y ∧ x.1 ≠ top ∧ y.1 ≠ top ∧
      EuclideanGeometry.angle (p x.1) (p i) (p y.1) ≤ delta * lam ∧
      delta * lam < EuclideanGeometry.angle (p i) (p x.1) (p y.1) ∧
      delta * lam < EuclideanGeometry.angle (p i) (p y.1) (p x.1) := by
  have htpos : 0 < t :=
    sendov_scale_pos (by omega : 1 ≤ n) hdelta0 ht
  have hlampos : 0 < lam := by
    rw [hlam]
    exact div_pos Real.pi_pos htpos
  obtain ⟨x, y, hxy, hxTop, hyTop, hsmall⟩ :=
    separated_support_two_has_small_pair_away_from_top
      hp hcap Cfam hcard hn hdelta0 hdeltaHalf
      ht hlam top hTop hit hI hsupport hsep
  have hix : i ≠ x.1 := x.2.symm
  have hiy : i ≠ y.1 := y.2.symm
  have hxyVal : x.1 ≠ y.1 := by
    intro heq
    exact hxy (Subtype.ext heq)
  obtain ⟨hxOuter, hyOuter⟩ :=
    both_outer_angles_ge_of_actual_small_angle
      hp hcap hix hiy hxyVal hsmall
  have hstrict :
      delta * lam < (1 - delta) * lam := by
    have hgap : 0 < (1 - 2 * delta) := by linarith
    nlinarith [mul_pos hgap hlampos]
  exact ⟨x, y, hxy, hxTop, hyTop, hsmall,
    hstrict.trans_le hxOuter,
    hstrict.trans_le hyOuter⟩

#print axioms outer_angle_ge_of_actual_small_angle
#print axioms both_outer_angles_ge_of_actual_small_angle
#print axioms separated_support_two_has_non_top_triangle_two_large_angles

end JSP000404Research
