
import JSP000404Research.PlanarStandardResidualBudget
import JSP000404Research.ResidualHardRemainder
import Mathlib.Tactic

/-!
# Genuine planar reduction to the concrete residual hard-word remainder

The residual projection route is now fully connected to the actual planar
Sendov centre exponents.

For an injective finite planar configuration in the nonintegral regime

  t = n + delta,  0 <= delta < 1,

use the generic projection order and its standard (n+1)-band residual
colouring.  ProjectionCutLocalCycle identifies the local DirectionData cyclic
exponent with the genuine centreExponent, and PlanarStandardResidualBudget
proves the required one-layer active-colour estimate.

Therefore all abstract hypotheses of ResidualHardRemainder are automatic.

The only remaining Boolean projection obligation is the concrete inequality

  card(saturatedOverlapWords)
    + card(lossCompletionWords)
      <=
  2^n - card(coveredCompletionWords).

Any proof of this hard-word-to-hole payment immediately gives the sharp
centre-level dyadic capacity.
-/

namespace JSP000404Research
namespace ProjectionOrdered

open OrderedEdgeColoring
open DirectionData
open scoped BigOperators

section

variable {V : Type*} [Fintype V]
variable {p : V → Plane}
variable (hp : Function.Injective p)

local instance projectionOrder :
    LinearOrder (ProjectionOrdered V) :=
  projectionLinearOrder hp

noncomputable def planarStandardResidualColoring
    {lam t delta : ℝ} {n : ℕ}
    (hcap : AngleCap p lam)
    (hn : 1 ≤ n)
    (hdelta0 : 0 ≤ delta)
    (hdelta1 : delta < 1)
    (ht : t = (n : ℝ) + delta)
    (hlam : lam = Real.pi / t) :
    OrderedEdgeColoring (ProjectionOrdered V) (n + 1) := by
  let htpos : 0 < t :=
    sendov_scale_pos hn hdelta0 ht
  let D :=
    genericDirectionData_sendov hp hcap htpos hlam
  have hwidth : t < (n + 1 : ℕ) := by
    rw [ht]
    exact_mod_cast (show
      (n : ℝ) + delta < (n : ℝ) + 1 by linarith)
  exact standardResidualColoring D n hwidth

def planarCentreExponent
    {t : ℝ}
    (C : ∀ i : ProjectionOrdered V,
      CentreProjectiveCycle
        (reindexedPoint_injective hp) i) :
    ProjectionOrdered V → ℕ :=
  fun i => centreExponent (C i) t

theorem planarCentreExponent_le_n
    {t delta : ℝ} {n : ℕ}
    (hn : 1 ≤ n)
    (hdelta0 : 0 ≤ delta)
    (hdelta1 : delta < 1)
    (ht : t = (n : ℝ) + delta)
    (C : ∀ i : ProjectionOrdered V,
      CentreProjectiveCycle
        (reindexedPoint_injective hp) i) :
    ∀ i, planarCentreExponent hp C i ≤ n := by
  intro i
  unfold planarCentreExponent
  have hlt :=
    centreExponent_lt_n
      (C i) n delta t
      hn hdelta0 hdelta1 ht
  omega

theorem planarStandardResidual_oneLayer_budget
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
    let R :=
      planarStandardResidualColoring
        hp hcap hn hdelta0 hdelta1 ht hlam
    ∀ i,
      (active R i).card ≤
        n - planarCentreExponent hp C i + 1 := by
  dsimp [planarStandardResidualColoring,
    planarCentreExponent]
  exact planarStandardResidual_oneLayer_family
    hp hcap hn hdelta0 hdelta1 ht hlam C

/-- Main genuine-planar hard remainder outlet. -/
theorem planar_centre_capacity_of_hard_words_fit_holes
    {lam t delta : ℝ} {n : ℕ}
    (hcap : AngleCap p lam)
    (hn : 1 ≤ n)
    (hdelta0 : 0 ≤ delta)
    (hdelta1 : delta < 1)
    (ht : t = (n : ℝ) + delta)
    (hlam : lam = Real.pi / t)
    (C : ∀ i : ProjectionOrdered V,
      CentreProjectiveCycle
        (reindexedPoint_injective hp) i)
    (hholes :
      let R :=
        planarStandardResidualColoring
          hp hcap hn hdelta0 hdelta1 ht hlam
      let exponent := planarCentreExponent hp C
      (saturatedOverlapWords R exponent).card +
          (lossCompletionWords R exponent).card
        ≤
      2 ^ n - (coveredCompletionWords R).card) :
    (∑ i : ProjectionOrdered V,
      2 ^ centreExponent (C i) t) ≤ 2 ^ n := by
  let R :=
    planarStandardResidualColoring
      hp hcap hn hdelta0 hdelta1 ht hlam
  let exponent := planarCentreExponent hp C
  have hexp :
      ∀ i, exponent i ≤ n :=
    planarCentreExponent_le_n
      hp hn hdelta0 hdelta1 ht C
  have hone :
      ∀ i, (active R i).card ≤
        n - exponent i + 1 := by
    exact planarStandardResidual_oneLayer_budget
      hp hcap hn hdelta0 hdelta1 ht hlam C
  have hcapCentre :
      (∑ i : ProjectionOrdered V, 2 ^ exponent i) ≤
        2 ^ n := by
    exact exponent_capacity_of_hard_words_fit_holes
      R exponent hexp hone hholes
  simpa [exponent, planarCentreExponent] using hcapCentre

#print axioms planarStandardResidualColoring
#print axioms planarCentreExponent_le_n
#print axioms planarStandardResidual_oneLayer_budget
#print axioms planar_centre_capacity_of_hard_words_fit_holes

end

end ProjectionOrdered
end JSP000404Research
