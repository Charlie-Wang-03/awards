import JSP000404Research.SupportThreeNonExposedMiddleHiddenCluster
import Mathlib.Tactic

/-!
# Two disjoint half-cap bridges forced by six-point middle-hidden geometry

The two zero-quotient adjacent ray pairs are BOTH strictly below
lambda/2, since their total actual angle is at most delta*lambda and
0 <= delta < 1/2. Every other cross-cluster angle is strictly larger
than lambda by the separately certified geometric argument.

This gives an unconditional-for-the-stated-configuration geometric
matching shape, but it does not provide outside Boolean true holes
or close the global dyadic capacity proof.
-/

namespace JSP000404Research

theorem nonexposed_middle_hidden_two_disjoint_halfcap_bridges
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane}
    {lam t delta : ℝ} {n : ℕ}
    {top i : V}
    (hp : Function.Injective p)
    (hcap : AngleCap p lam)
    (C : CentreProjectiveCycle hp i)
    (hcard : Fintype.card V = 6)
    (hn : 4 ≤ n)
    (hdelta0 : 0 ≤ delta)
    (hdeltaHalf : delta < (1 : ℝ) / 2)
    (ht : t = (n : ℝ) + delta)
    (hlam : lam = Real.pi / t)
    (hit : i ≠ top)
    (hexp : centreExponent C t = n - 3)
    (hsupport : positiveSupport (centreQuotient C t) = 3)
    (hmiddle : SupportThreePinnedMiddleShape (t := t) hp
      (Ne.symm hit) C)
    (hnot : ¬ StrictlyExposedAt p i) :
    ∃ r b c d : OtherVertex i,
      r ≠ b ∧ r ≠ c ∧ r ≠ d ∧
      b ≠ c ∧ b ≠ d ∧ c ≠ d ∧
      EuclideanGeometry.angle (p r.1) (p i) (p b.1) < lam / 2 ∧
      EuclideanGeometry.angle (p c.1) (p i) (p d.1) < lam / 2 ∧
      lam < EuclideanGeometry.angle (p top) (p i) (p r.1) ∧
      lam < EuclideanGeometry.angle (p top) (p i) (p b.1) ∧
      lam < EuclideanGeometry.angle (p top) (p i) (p c.1) ∧
      lam < EuclideanGeometry.angle (p top) (p i) (p d.1) ∧
      lam < EuclideanGeometry.angle (p r.1) (p i) (p c.1) ∧
      lam < EuclideanGeometry.angle (p r.1) (p i) (p d.1) ∧
      lam < EuclideanGeometry.angle (p b.1) (p i) (p c.1) ∧
      lam < EuclideanGeometry.angle (p b.1) (p i) (p d.1) := by
  obtain ⟨r, b, c, d,
    _hrTop, _hbTop, _hcTop, _hdTop,
    hrb, hrc, hrd, hbc, hbd, hcd,
    hsmall, hTopR, hTopB, hTopC, hTopD,
    hRC, hRD, hBC, hBD⟩ :=
    nonexposed_support_three_middle_hidden_cluster_angles_gt_lam
      hp hcap C hcard hn hdelta0 hdeltaHalf
      ht hlam hit hexp hsupport hmiddle hnot
  have htpos : 0 < t := by
    rw [ht]
    have hnR : (4 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    linarith
  have hlampos : 0 < lam := by
    rw [hlam]
    exact div_pos Real.pi_pos htpos
  have hscaled : delta * lam < lam / 2 := by
    have hlt := mul_lt_mul_of_pos_right hdeltaHalf hlampos
    nlinarith
  have hangle1 :
      0 ≤ EuclideanGeometry.angle (p r.1) (p i) (p b.1) :=
    EuclideanGeometry.angle_nonneg _ _ _
  have hangle2 :
      0 ≤ EuclideanGeometry.angle (p c.1) (p i) (p d.1) :=
    EuclideanGeometry.angle_nonneg _ _ _
  have hshort1 :
      EuclideanGeometry.angle (p r.1) (p i) (p b.1) < lam / 2 := by
    linarith
  have hshort2 :
      EuclideanGeometry.angle (p c.1) (p i) (p d.1) < lam / 2 := by
    linarith
  exact ⟨r, b, c, d, hrb, hrc, hrd, hbc, hbd, hcd,
    hshort1, hshort2,
    hTopR, hTopB, hTopC, hTopD, hRC, hRD, hBC, hBD⟩

#print axioms nonexposed_middle_hidden_two_disjoint_halfcap_bridges

end JSP000404Research
