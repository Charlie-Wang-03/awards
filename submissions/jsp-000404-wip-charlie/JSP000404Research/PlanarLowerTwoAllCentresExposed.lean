import JSP000404Research.SupportLeTwoTransitionInterval
import JSP000404Research.CentreExponentBounds
import Mathlib.Tactic

/-!
# Genuine n=2 lower branch: EVERY original centre is strictly exposed

Unlike a conditional four-centre lemma, this is a geometric conclusion from
the actual AngleCap, concrete centre cycles and their real quotient sums.

At t=2+delta, 0<=delta<1/2, each true centre quotient sum is <=2.
Since floorExcess + positiveSupport = quotient sum, the actual positive
support at each centre is <=2. The certified support<=2 transition theorem
then shows that every centre is strictly exposed by a supporting direction.

This removes interior-vertex obstructions without requiring an extra
geometry premise. For a four-point lower-branch theorem, the remaining
planar combinatorial step is to realize a crossing pair of diagonals
from four strictly exposed points, then apply the already-verified
CrossingDiagonalsQuadrilateralAngleSum and sharp-angle budget.
-/

namespace JSP000404Research

theorem lower_two_all_centres_strictlyExposed
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane}
    (hp : Function.Injective p)
    {lam t delta : ℝ}
    (hcap : AngleCap p lam)
    (hdelta0 : 0 ≤ delta)
    (hdeltaHalf : delta < (1 : ℝ) / 2)
    (ht : t = (2 : ℝ) + delta)
    (hlam : lam = Real.pi / t)
    (C : ∀ i : V, CentreProjectiveCycle hp i)
    (i : V) :
    StrictlyExposedAt p i := by
  have hdelta1 : delta < 1 := by linarith
  have htpos : 0 < t := by rw [ht]; linarith
  have htone : (1 : ℝ) ≤ t := by rw [ht]; linarith
  let q := centreQuotient (C i) t
  have hmass : (∑ r, q r) ≤ 2 :=
    centreQuotient_function_sum_le_n
      (C i) 2 delta t (by omega) hdelta0 hdelta1
      (by simpa only [Nat.cast_ofNat] using ht)
  have hid := floorExcess_add_positiveSupport q
  have hsupport : positiveSupport q ≤ 2 := by omega
  exact strictlyExposedAt_of_positiveSupport_le_two
    hp hcap htpos htone hlam i (C i) hsupport

#print axioms lower_two_all_centres_strictlyExposed

end JSP000404Research
