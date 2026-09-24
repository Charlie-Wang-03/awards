import JSP000404Research.CentreExponent
import JSP000404Research.SupportTwoDeletion
import Mathlib.Data.List.OfFn
import Mathlib.Tactic

/-!
# Function-valued centre exponent equals quotient-list exponent

The centre arithmetic uses floorExcess on the finite quotient function, while
the cut/rotation modules use listExponent on its List.ofFn representation.

These are definitionally the same finite sum.
-/

namespace JSP000404Research

theorem listExponent_ofFn_eq_floorExcess
    {m : ℕ} (q : Fin m → ℕ) :
    listExponent (List.ofFn q) = floorExcess q := by
  unfold listExponent floorExcess excess
  rw [← List.sum_ofFn]
  simp [List.map_ofFn, Function.comp_def]

theorem centreExponent_eq_listExponent
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane} {hp : Function.Injective p} {i : V}
    (C : CentreProjectiveCycle hp i)
    (t : ℝ) :
    centreExponent C t =
      listExponent (quotientList t C.gaps) := by
  unfold centreExponent
  rw [← listExponent_ofFn_eq_floorExcess,
      centreQuotient_ofFn]

#print axioms listExponent_ofFn_eq_floorExcess
#print axioms centreExponent_eq_listExponent

end JSP000404Research
