import JSP000404Research.PlanarKnownSmallCentreCapacity
import JSP000404Research.CentreExponentBounds
import Mathlib.Tactic

/-!
# Genuine n = 2, four original centres, no top-layer exponent

At t=2+delta, 0<=delta<1/2, every genuine centre exponent is <2.
If none of the four actual centres has exponent 1, all exponents vanish.
The resulting dyadic capacity is exact: four terms of weight 1 sum to 4.

This is a *conditional* no-top subcase. Its hypothesis is not claimed to
follow from AngleCap in the general four-centre configuration.
-/

namespace JSP000404Research
namespace ProjectionOrdered

theorem planar_lower_branch_n_two_four_no_top_capacity
    {V : Type*} [Fintype V]
    {p : V → Plane}
    (hp : Function.Injective p)
    {lam t delta : ℝ}
    (hcap : AngleCap p lam)
    (hcard : Fintype.card (ProjectionOrdered V) = 4)
    (hdelta0 : 0 ≤ delta)
    (hdeltaHalf : delta < (1 : ℝ) / 2)
    (ht : t = (2 : ℝ) + delta)
    (hlam : lam = Real.pi / t)
    (cycles :
      letI : LinearOrder (ProjectionOrdered V) := projectionLinearOrder hp
      ∀ i : ProjectionOrdered V,
        CentreProjectiveCycle (reindexedPoint_injective hp) i)
    (hnoTop :
      letI : LinearOrder (ProjectionOrdered V) := projectionLinearOrder hp
      ∀ i : ProjectionOrdered V, centreExponent (cycles i) t ≠ 1) :
    letI : LinearOrder (ProjectionOrdered V) := projectionLinearOrder hp
    (∑ i : ProjectionOrdered V,
      2 ^ centreExponent (cycles i) t) ≤ (2 : ℕ) ^ 2 := by
  letI : LinearOrder (ProjectionOrdered V) := projectionLinearOrder hp
  have hdelta1 : delta < 1 := by linarith
  have hzero :
      ∀ i : ProjectionOrdered V, centreExponent (cycles i) t = 0 := by
    intro i
    have hlt :
        centreExponent (cycles i) t < 2 :=
      centreExponent_lt_n
        (cycles i) 2 delta t (by omega)
        hdelta0 hdelta1
        (by simpa only [Nat.cast_ofNat] using ht)
    have hne := hnoTop i
    omega
  calc
    (∑ i : ProjectionOrdered V, 2 ^ centreExponent (cycles i) t)
        = ∑ _i : ProjectionOrdered V, (1 : ℕ) := by
          apply Finset.sum_congr rfl
          intro i _
          simp [hzero i]
    _ = Fintype.card (ProjectionOrdered V) := by simp
    _ = 4 := hcard
    _ ≤ (2 : ℕ) ^ 2 := by norm_num

#print axioms planar_lower_branch_n_two_four_no_top_capacity

end ProjectionOrdered
end JSP000404Research
