import JSP000404Research.CutMergedTwoBadRigidity
import JSP000404Research.CutMergedTwoBadSmallAngles
import JSP000404Research.SixPointBadSharedC4Colour
import Mathlib.Tactic

/-!
# Single certificate for the six-centre, two-saturation-bad, uncovered cut

Under actual AngleCap, the original centre exponent profile (top n-1,
all others n-3), an uncovered global unit cut, top safe, and exactly two
bad minima, the following consequences hold SIMULTANEOUSLY:

* the top centre is genuinely sharp;
* a single non-root colour has a C4 on the five minima and is active
  at both bad centres;
* each bad centre has its own actual strict sub-lambda small angle
  between two DISTINCT non-top other centres;
* two DISTINCT canonical global turn-unit slots at these bad centres
  are bad at the very same phase.

There is NO extra hypothesis of a root, a C4, a small angle, or a
chosen exceptional turn slot. This is a local structural certificate,
not the original all-cardinality six-source true-hole payment.
-/

namespace JSP000404Research
open BinaryEdgePartition

theorem six_point_uncovered_cut_two_bad_full_local_certificate
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane} (hp : Function.Injective p)
    {lam t delta c : ℝ} {n : ℕ}
    (hcap : AngleCap p lam)
    (C : ∀ v : V, CentreProjectiveCycle hp v)
    (hn : 4 ≤ n)
    (htpos : 0 < t)
    (hlam : lam = Real.pi / t)
    (ht : t = (n : ℝ) + delta)
    (hdelta0 : 0 ≤ delta)
    (hdeltaHalf : delta < (1 : ℝ) / 2)
    (hc0 : 0 ≤ c) (hcpi : c < Real.pi)
    (hcard : Fintype.card V = 6)
    (top bad₁ bad₂ : V)
    (htb₁ : top ≠ bad₁) (htb₂ : top ≠ bad₂)
    (hb₁₂ : bad₁ ≠ bad₂)
    (hTopExp : centreExponent (C top) t = n - 1)
    (hMinExp : ∀ v : V, v ≠ top →
      centreExponent (C v) t = n - 3)
    (huncovered :
      ∀ u : GlobalUnitGapSlot C t,
        ¬ GlobalCyclicCriticalUnitBadAt
          C t delta u (t * c / Real.pi))
    (hTopSafe :
      ¬ CutSaturationBadAt hp hcap C htpos hlam ht hdelta0
        (by linarith : delta < 1) hc0 hcpi top)
    (hBad₁ :
      CutSaturationBadAt hp hcap C htpos hlam ht hdelta0
        (by linarith : delta < 1) hc0 hcpi bad₁)
    (hBad₂ :
      CutSaturationBadAt hp hcap C htpos hlam ht hdelta0
        (by linarith : delta < 1) hc0 hcpi bad₂)
    (hOtherSafe :
      ∀ v : V, v ≠ top → v ≠ bad₁ → v ≠ bad₂ →
        ¬ CutSaturationBadAt hp hcap C htpos hlam ht hdelta0
          (by linarith : delta < 1) hc0 hcpi v) :
    let M :=
      uncoveredCutMergedPartition hp hcap C (by omega : 1 ≤ n)
        htpos hlam ht hdelta0 hdeltaHalf hc0 hcpi huncovered
    SharpAt p delta lam top ∧
    ∃ root colour : Fin n,
      colour ≠ root ∧
      colour ∈ active M bad₁ ∧
      colour ∈ active M bad₂ ∧
      HasFourCycle (localColourGraph M top colour) ∧
      ∃ u₁ u₂ : GlobalTurnUnitSlot C t,
        u₁.1 = bad₁ ∧ u₂.1 = bad₂ ∧ u₁ ≠ u₂ ∧
        GlobalCyclicTurnUnitBadAt C t delta u₁ (t * c / Real.pi) ∧
        GlobalCyclicTurnUnitBadAt C t delta u₂ (t * c / Real.pi) ∧
        ∃ x₁ y₁ x₂ y₂ : V,
          x₁ ≠ top ∧ x₁ ≠ bad₁ ∧
          y₁ ≠ top ∧ y₁ ≠ bad₁ ∧ x₁ ≠ y₁ ∧
          EuclideanGeometry.angle (p x₁) (p bad₁) (p y₁) < lam ∧
          x₂ ≠ top ∧ x₂ ≠ bad₂ ∧
          y₂ ≠ top ∧ y₂ ≠ bad₂ ∧ x₂ ≠ y₂ ∧
          EuclideanGeometry.angle (p x₂) (p bad₂) (p y₂) < lam := by
  dsimp only
  let M :=
    uncoveredCutMergedPartition hp hcap C (by omega : 1 ≤ n)
      htpos hlam ht hdelta0 hdeltaHalf hc0 hcpi huncovered
  obtain ⟨hSharp, root, hrootTop, _hrootAll, hrootEdges,
      hredBad₁, hredBad₂, hredOther,
      u₁,u₂,hu₁Centre,hu₂Centre,huNe,hu₁Bad,hu₂Bad⟩ :=
    uncovered_cut_two_bad_minima_rigidity
      hp hcap C hn htpos hlam ht hdelta0 hdeltaHalf
      hc0 hcpi hcard top bad₁ bad₂
      htb₁ htb₂ hb₁₂ hTopExp hMinExp
      huncovered hTopSafe hBad₁ hBad₂ hOtherSafe
  obtain ⟨colour,hcroot,hcBad₁,hcBad₂,hC4⟩ :=
    two_bad_minima_share_monochromatic_fourCycle_colour
      M top bad₁ bad₂ root
      htb₁ htb₂ hb₁₂ hcard
      hrootTop hrootEdges hredBad₁ hredBad₂ hredOther
  obtain ⟨x₁,y₁,x₂,y₂,
      hx₁Top,hx₁Bad,hy₁Top,hy₁Bad,hx₁y₁,ha₁,
      hx₂Top,hx₂Bad,hy₂Top,hy₂Bad,hx₂y₂,ha₂⟩ :=
    uncovered_cut_two_bad_minima_have_small_nonTop_angles
      hp hcap C hn htpos hlam ht hdelta0 hdeltaHalf
      hc0 hcpi hcard top bad₁ bad₂
      htb₁ htb₂ hb₁₂ hTopExp hMinExp
      huncovered hTopSafe hBad₁ hBad₂ hOtherSafe
  exact ⟨hSharp,root,colour,hcroot,hcBad₁,hcBad₂,hC4,
    u₁,u₂,hu₁Centre,hu₂Centre,huNe,hu₁Bad,hu₂Bad,
    x₁,y₁,x₂,y₂,hx₁Top,hx₁Bad,hy₁Top,hy₁Bad,hx₁y₁,ha₁,
    hx₂Top,hx₂Bad,hy₂Top,hy₂Bad,hx₂y₂,ha₂⟩

#print axioms six_point_uncovered_cut_two_bad_full_local_certificate
end JSP000404Research
