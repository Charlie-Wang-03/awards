
import JSP000404Research.ProjectionCutLocalCycle
import JSP000404Research.CentreExponentBounds
import JSP000404Research.StandardResidual
import Mathlib.Tactic

/-!
# Genuine planar one-layer budget for the standard residual colouring

The preceding projection modules now close the full representation chain:

  planar configuration
    -> generic projection order
    -> DirectionData
    -> explicit projective-cut LocalDirectionCycle
    -> genuine centreExponent.

LocalDirectionCycle gives

  centreExponent(i) + card incidentBands_{n+1}(i) <= n+1.

The standard residual colouring has exactly those incident bands as its active
palette.  Therefore every genuine Sendov centre satisfies

  card(active(i)) <= n-centreExponent(i)+1

throughout the full nonintegral range

  t=n+delta, 0<=delta<1.

This removes the abstract one-layer hypothesis from the residual projection
route for actual planar configurations.
-/

namespace JSP000404Research
namespace ProjectionOrdered

open OrderedEdgeColoring
open DirectionData

section

variable {V : Type*} [Fintype V]
variable {p : V → Plane}
variable (hp : Function.Injective p)

local instance projectionOrder :
    LinearOrder (ProjectionOrdered V) :=
  projectionLinearOrder hp

theorem planarStandardResidual_active_card_le_oneLayer
    {lam t delta : ℝ} {n : ℕ}
    (hcap : AngleCap p lam)
    (hn : 1 ≤ n)
    (hdelta0 : 0 ≤ delta)
    (hdelta1 : delta < 1)
    (ht : t = (n : ℝ) + delta)
    (hlam : lam = Real.pi / t)
    (i : ProjectionOrdered V)
    (C : CentreProjectiveCycle
      (reindexedPoint_injective hp) i) :
    let D :=
      genericDirectionData_sendov hp hcap
        (sendov_scale_pos hn hdelta0 ht) hlam
    let hwidth : t < (n + 1 : ℕ) := by
      rw [ht]
      exact_mod_cast (show
        (n : ℝ) + delta < (n : ℝ) + 1 by linarith)
    (active (standardResidualColoring D n hwidth) i).card
      ≤
    n - centreExponent C t + 1 := by
  let htpos : 0 < t :=
    sendov_scale_pos hn hdelta0 ht
  let D :=
    genericDirectionData_sendov hp hcap htpos hlam
  have hwidthR : t < (n : ℝ) + 1 := by
    rw [ht]
    linarith
  have hwidthN : t < (n + 1 : ℕ) := by
    exact_mod_cast hwidthR
  let L :=
    projectionCutLocalCycle hp hcap htpos hlam i C
  have hagree :
      L.exponent = centreExponent C t :=
    projectionCutLocalCycle_exponent_eq_centreExponent
      hp hcap htpos hlam i C
  have hexp :
      centreExponent C t ≤ n := by
    have hlt :=
      centreExponent_lt_n C n delta t
        hn hdelta0 hdelta1 ht
    omega
  have hbudget :=
    standardActive_card_le_centreDeficit_add_one_of_local_agreement
      D L C hwidthR hexp hagree
  simpa [D, DirectionData.standardResidualColoring] using hbudget

/-- Family form used directly by residual projection modules. -/
theorem planarStandardResidual_oneLayer_family
    {lam t delta : ℝ} {n : ℕ}
    (hcap : AngleCap p lam)
    (hn : 1 ≤ n)
    (hdelta0 : 0 ≤ delta)
    (hdelta1 : delta < 1)
    (ht : t = (n : ℝ) + delta)
    (hlam : lam = Real.pi / t)
    (C : ∀ i : ProjectionOrdered V,
      CentreProjectiveCycle
        (reindexedPoint_injective hp) i) :
    let htpos : 0 < t :=
      sendov_scale_pos hn hdelta0 ht
    let D :=
      genericDirectionData_sendov hp hcap htpos hlam
    let hwidth : t < (n + 1 : ℕ) := by
      rw [ht]
      exact_mod_cast (show
        (n : ℝ) + delta < (n : ℝ) + 1 by linarith)
    ∀ i,
      (active (standardResidualColoring D n hwidth) i).card
        ≤
      n - centreExponent (C i) t + 1 := by
  dsimp
  intro i
  exact planarStandardResidual_active_card_le_oneLayer
    hp hcap hn hdelta0 hdelta1 ht hlam i (C i)

#print axioms planarStandardResidual_active_card_le_oneLayer
#print axioms planarStandardResidual_oneLayer_family

end

end ProjectionOrdered
end JSP000404Research
