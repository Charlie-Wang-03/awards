import JSP000404Research.SupportThreeMiddleHiddenLargeBridge
import JSP000404Research.MiddleHiddenClusterSeparation
import Mathlib.Tactic

/-!
# Six-centre support-three middle-hidden geometry: full cluster separation

The native positive-quotient angle lower bounds and the zero-quotient
actual-angle mass bound form one canonical geometric certificate.
The five rays are split into {top}, {r,b} and {c,d}, with
small in-cluster edges r--b and c--d and all eight inter-cluster
angles STRICTLY above the Sendov scale lambda.

No claim that the entire six-source Boolean debt is paid follows
from this angular fact. The global WIP remains open.
-/

namespace JSP000404Research

theorem support_three_middle_hidden_all_cross_cluster_angles_gt_lam
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
    (hthree :
      ∃ first rest, C.rays = first :: rest ∧
        boolTransitionCountFrom
          (raySignAt hp i first)
          (liftedCentreSignPath hp i first rest) = 3) :
    ∃ r b c d : OtherVertex i,
      r.1 ≠ top ∧ b.1 ≠ top ∧ c.1 ≠ top ∧ d.1 ≠ top ∧
      r ≠ b ∧ r ≠ c ∧ r ≠ d ∧
      b ≠ c ∧ b ≠ d ∧ c ≠ d ∧
      EuclideanGeometry.angle (p r.1) (p i) (p b.1) +
        EuclideanGeometry.angle (p c.1) (p i) (p d.1)
        ≤ delta * lam ∧
      lam < EuclideanGeometry.angle (p top) (p i) (p r.1) ∧
      lam < EuclideanGeometry.angle (p top) (p i) (p b.1) ∧
      lam < EuclideanGeometry.angle (p top) (p i) (p c.1) ∧
      lam < EuclideanGeometry.angle (p top) (p i) (p d.1) ∧
      lam < EuclideanGeometry.angle (p r.1) (p i) (p c.1) ∧
      lam < EuclideanGeometry.angle (p r.1) (p i) (p d.1) ∧
      lam < EuclideanGeometry.angle (p b.1) (p i) (p c.1) ∧
      lam < EuclideanGeometry.angle (p b.1) (p i) (p d.1) := by
  obtain ⟨r, b, c, d,
    hrTop, hbTop, hcTop, hdTop,
    hrb, hrc, hrd, hbc, hbd, hcd,
    hsmall, hTopR, hBridge, hDTop⟩ :=
    support_three_middle_hidden_large_bridge
      hp hcap C hcard hn hdelta0 hdeltaHalf
      ht hlam hit hexp hsupport hmiddle hthree
  have htpos : 0 < t := by
    rw [ht]
    have hnR : (4 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    linarith
  have hlampos : 0 < lam := by
    rw [hlam]
    exact div_pos Real.pi_pos htpos
  have hcluster :=
    middle_hidden_cluster_separation
      (p := p) (i := i) (top := top)
      (r := r.1) (b := b.1) (c := c.1) (d := d.1)
      hdelta0 hlampos hsmall hTopR hBridge hDTop
  exact ⟨r, b, c, d,
    hrTop, hbTop, hcTop, hdTop,
    hrb, hrc, hrd, hbc, hbd, hcd,
    hsmall, hcluster⟩

#print axioms support_three_middle_hidden_all_cross_cluster_angles_gt_lam

end JSP000404Research
