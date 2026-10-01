import JSP000404Research.ProjectionUnitSupportTwoConsecutiveBands
import JSP000404Research.SecondLayerExactTwoSkinnyTerminal
import Mathlib.Tactic

/-!
# Rigid exact-two support terminal in projection order

For four distinct second-layer centres with exactly two support-one and two
support-two members, assume the two support-two members are projected-loss
vertices of the standard residual colouring.

Four-centre packing supplies unit transition certificates at the two
support-two centres.  Projected-loss band rigidity then forces each local
occupied palette to be three consecutive bands, while the same unit
transition certificates force a skinny triangle at each support-two centre.
-/

namespace JSP000404Research
namespace ProjectionOrdered

theorem exactTwo_support_projectedLoss_rigid_terminal
    {V : Type*} [Fintype V]
    {p : V → Plane}
    (hp : Function.Injective p)
    {lam t delta : ℝ} {n : ℕ}
    (hcap : AngleCap p lam)
    (hn3 : 3 ≤ n)
    (hdelta0 : 0 ≤ delta)
    (hdeltaHalf : delta < (1 : ℝ) / 2)
    (ht : t = (n : ℝ) + delta)
    (hlam : lam = Real.pi / t)
    (C :
      ∀ i : ProjectionOrdered V,
        CentreProjectiveCycle (reindexedPoint_injective hp) i)
    {o₁ o₂ s₁ s₂ : ProjectionOrdered V}
    (ho12 : o₁ ≠ o₂)
    (ho1s1 : o₁ ≠ s₁) (ho1s2 : o₁ ≠ s₂)
    (ho2s1 : o₂ ≠ s₁) (ho2s2 : o₂ ≠ s₂)
    (hs12 : s₁ ≠ s₂)
    (ho1Second : centreExponent (C o₁) t = n - 2)
    (ho2Second : centreExponent (C o₂) t = n - 2)
    (hs1Second : centreExponent (C s₁) t = n - 2)
    (hs2Second : centreExponent (C s₂) t = n - 2)
    (ho1Support :
      positiveSupport (centreQuotient (C o₁) t) = 1)
    (ho2Support :
      positiveSupport (centreQuotient (C o₂) t) = 1)
    (hs1Support :
      positiveSupport (centreQuotient (C s₁) t) = 2)
    (hs2Support :
      positiveSupport (centreQuotient (C s₂) t) = 2)
    (hs1Loss :
      s₁ ∈ projectedLossVertices
        (planarStandardResidualColoring
          hp hcap (by omega : 1 ≤ n)
          hdelta0 (by linarith : delta < 1) ht hlam)
        (planarCentreExponent hp C))
    (hs2Loss :
      s₂ ∈ projectedLossVertices
        (planarStandardResidualColoring
          hp hcap (by omega : 1 ≤ n)
          hdelta0 (by linarith : delta < 1) ht hlam)
        (planarCentreExponent hp C)) :
    let htpos : 0 < t :=
      sendov_scale_pos (by omega : 1 ≤ n) hdelta0 ht
    let L₁ :=
      projectionCutLocalCycle hp hcap htpos hlam s₁ (C s₁)
    let L₂ :=
      projectionCutLocalCycle hp hcap htpos hlam s₂ (C s₂)
    ∃ cert₁ :
        HighExponentTransitionIntervalCertificate
          (reindexedPoint_injective hp) t s₁ (C s₁),
    ∃ cert₂ :
        HighExponentTransitionIntervalCertificate
          (reindexedPoint_injective hp) t s₂ (C s₂),
    ∃ m₁ m₂ : ℕ,
      cert₁.qe = 1 ∧
      cert₂.qe = 1 ∧
      (n - 1 ∈ quotientList t (C s₁).gaps) ∧
      (n - 1 ∈ quotientList t (C s₂).gaps) ∧
      occupiedNatBands L₁.values = {m₁,m₁+1,m₁+2} ∧
      occupiedNatBands L₂.values = {m₂,m₂+1,m₂+2} ∧
      SupportTwoSkinnyTriangle (reindexedPoint p) lam n s₁ ∧
      SupportTwoSkinnyTriangle (reindexedPoint p) lam n s₂ := by
  letI : LinearOrder (ProjectionOrdered V) :=
    projectionLinearOrder hp
  have hcapR :
      AngleCap (reindexedPoint p) lam :=
    angleCap_reindexed hcap

  obtain ⟨cert₁,cert₂,hq1,hq2,hhidden1,hhidden2⟩ :=
    twoSupportOne_twoSupportTwo_transition_qe_eq_one
      (p := reindexedPoint p)
      (reindexedPoint_injective hp)
      hcapR hn3 hdelta0 hdeltaHalf ht hlam
      ho12 ho1s1 ho1s2 ho2s1 ho2s2 hs12
      (C o₁) (C o₂) (C s₁) (C s₂)
      ho1Second ho2Second hs1Second hs2Second
      ho1Support ho2Support hs1Support hs2Support

  have hs1Loss' :
      s₁ ∈ projectedLossVertices
        (let htpos : 0 < t :=
          sendov_scale_pos (by omega : 1 ≤ n) hdelta0 ht
         let D :=
          genericDirectionData_sendov hp hcap htpos hlam
         let hwidth : t < (n + 1 : ℕ) := by
           rw [ht]
           exact_mod_cast
             (show (n : ℝ) + delta < (n : ℝ) + 1 by linarith)
         standardResidualColoring D n hwidth)
        (fun q => centreExponent (C q) t) := by
    simpa [planarStandardResidualColoring,
      planarCentreExponent] using hs1Loss

  have hs2Loss' :
      s₂ ∈ projectedLossVertices
        (let htpos : 0 < t :=
          sendov_scale_pos (by omega : 1 ≤ n) hdelta0 ht
         let D :=
          genericDirectionData_sendov hp hcap htpos hlam
         let hwidth : t < (n + 1 : ℕ) := by
           rw [ht]
           exact_mod_cast
             (show (n : ℝ) + delta < (n : ℝ) + 1 by linarith)
         standardResidualColoring D n hwidth)
        (fun q => centreExponent (C q) t) := by
    simpa [planarStandardResidualColoring,
      planarCentreExponent] using hs2Loss

  obtain ⟨m₁,hm1⟩ :=
    planar_projectedLoss_unitSupportTwo_threeBands_consecutive
      hp hcap hn3 hdelta0 hdeltaHalf ht hlam
      C s₁ hs1Loss' hs1Second hs1Support cert₁ hq1

  obtain ⟨m₂,hm2⟩ :=
    planar_projectedLoss_unitSupportTwo_threeBands_consecutive
      hp hcap hn3 hdelta0 hdeltaHalf ht hlam
      C s₂ hs2Loss' hs2Second hs2Support cert₂ hq2

  have hskinny :=
    twoSupportOne_twoSupportTwo_force_two_skinny_triangles
      (p := reindexedPoint p)
      (reindexedPoint_injective hp)
      hcapR hn3 hdelta0 hdeltaHalf ht hlam
      ho12 ho1s1 ho1s2 ho2s1 ho2s2 hs12
      (C o₁) (C o₂) (C s₁) (C s₂)
      ho1Second ho2Second hs1Second hs2Second
      ho1Support ho2Support hs1Support hs2Support

  exact ⟨cert₁,cert₂,m₁,m₂,
    hq1,hq2,hhidden1,hhidden2,
    hm1,hm2,hskinny.1,hskinny.2⟩

#print axioms exactTwo_support_projectedLoss_rigid_terminal

end ProjectionOrdered
end JSP000404Research
