import JSP000404Research.SmallCentreCapacity
import JSP000404Research.ProjectionThreeCentreCapacity
import JSP000404Research.ProjectionFourCentreCapacity
import Mathlib.Tactic

/-!
# Precisely certified small-original-centre branches of the global capacity

This combines three independently kernel-verified genuine planar results,
without pretending that any general outside-TRUE-hole payment holds:

  card ProjectionOrdered V <= 2     (n >= 1),
  card ProjectionOrdered V  = 3     (n >= 2),
  card ProjectionOrdered V  = 4     (n >= 3).

Every other configuration remains outside the certified small-cardinality
subcase and is NOT discharged by this lemma.
-/

namespace JSP000404Research
namespace ProjectionOrdered

theorem planar_lower_branch_known_small_centre_dyadic_capacity
    {V : Type*} [Fintype V]
    {p : V → Plane}
    (hp : Function.Injective p)
    {lam t delta : ℝ} {n : ℕ}
    (hcap : AngleCap p lam)
    (hn : 1 ≤ n)
    (hdelta0 : 0 ≤ delta)
    (hdeltaHalf : delta < (1 : ℝ) / 2)
    (ht : t = (n : ℝ) + delta)
    (hlam : lam = Real.pi / t)
    (cycles :
      letI : LinearOrder (ProjectionOrdered V) := projectionLinearOrder hp
      ∀ i : ProjectionOrdered V,
        CentreProjectiveCycle (reindexedPoint_injective hp) i)
    (hknown :
      Fintype.card (ProjectionOrdered V) ≤ 2 ∨
      (Fintype.card (ProjectionOrdered V) = 3 ∧ 2 ≤ n) ∨
      (Fintype.card (ProjectionOrdered V) = 4 ∧ 3 ≤ n)) :
    letI : LinearOrder (ProjectionOrdered V) := projectionLinearOrder hp
    (∑ i : ProjectionOrdered V,
      2 ^ centreExponent (cycles i) t) ≤ 2 ^ n := by
  letI : LinearOrder (ProjectionOrdered V) := projectionLinearOrder hp
  rcases hknown with hTwo | hThree | hFour
  · exact planar_lower_branch_card_le_two_dyadic_capacity
      hp hTwo hn hdelta0 hdeltaHalf ht cycles
  · exact planar_lower_branch_card_three_dyadic_capacity
      hp hcap hThree.1 hThree.2
      hdelta0 hdeltaHalf ht hlam cycles
  · exact planar_lower_branch_card_four_dyadic_capacity
      hp hcap hFour.1 hFour.2
      hdelta0 hdeltaHalf ht hlam cycles

#print axioms planar_lower_branch_known_small_centre_dyadic_capacity

end ProjectionOrdered
end JSP000404Research
