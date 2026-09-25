
import JSP000404Research.StableCyclicSupport
import JSP000404Research.CentreExponent
import JSP000404Research.SupportListBridge
import Mathlib.Data.List.OfFn
import Mathlib.Tactic

/-!
# List/function bridge for cyclic positive support

The concrete projective cycle is naturally stored as a quotient list, while
StableCyclicSupport is indexed by Fin m.

For any list qs, its get-function has exactly the same positive-support count.
Thus cyclic separation of qs.get immediately yields the half-length support
bound on the original list.

For a concrete centre, centreQuotient is exactly the get-function of the
canonical quotient list.
-/

namespace JSP000404Research

theorem positiveSupport_get_eq_listPositiveCount
    (qs : List ℕ) :
    positiveSupport qs.get = listPositiveCount qs := by
  have h :=
    listPositiveCount_ofFn_eq_positiveSupport
      (q := qs.get)
  simpa using h.symm

/-- List form of the cyclic independent-support theorem. -/
theorem listPositiveCount_mul_two_le_length_of_cyclicSeparated
    (qs : List ℕ)
    (hsep : CyclicSeparatedPositive qs.get) :
    2 * listPositiveCount qs ≤ qs.length := by
  have h :=
    positiveSupport_mul_two_le_length_of_cyclicSeparated
      qs.get hsep
  rw [positiveSupport_get_eq_listPositiveCount] at h
  exact h

theorem listPositiveCount_le_half_length_of_cyclicSeparated
    (qs : List ℕ)
    (hsep : CyclicSeparatedPositive qs.get) :
    listPositiveCount qs ≤ qs.length / 2 := by
  have h :=
    listPositiveCount_mul_two_le_length_of_cyclicSeparated
      qs hsep
  omega

/-- The finite-function centre quotient agrees pointwise with the canonical
quotient list. -/
theorem centreQuotient_eq_quotientList_get
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane} {hp : Function.Injective p} {i : V}
    (C : CentreProjectiveCycle hp i)
    (t : ℝ) :
    centreQuotient C t =
      (quotientList t C.gaps).get := by
  funext r
  unfold centreQuotient quotientList
  simp

/-- Hence concrete cyclic separation can be stated interchangeably on the
centreQuotient function or on the quotient-list get-function. -/
theorem cyclicSeparated_centreQuotient_iff_list_get
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane} {hp : Function.Injective p} {i : V}
    (C : CentreProjectiveCycle hp i)
    (t : ℝ) :
    CyclicSeparatedPositive (centreQuotient C t) ↔
      CyclicSeparatedPositive
        (quotientList t C.gaps).get := by
  rw [centreQuotient_eq_quotientList_get]

/-- Concrete list support count is exactly concrete finite support. -/
theorem listPositiveCount_centreQuotientList
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane} {hp : Function.Injective p} {i : V}
    (C : CentreProjectiveCycle hp i)
    (t : ℝ) :
    listPositiveCount (quotientList t C.gaps) =
      positiveSupport (centreQuotient C t) := by
  rw [centreQuotient_ofFn C t,
      listPositiveCount_ofFn_eq_positiveSupport]

#print axioms positiveSupport_get_eq_listPositiveCount
#print axioms listPositiveCount_mul_two_le_length_of_cyclicSeparated
#print axioms centreQuotient_eq_quotientList_get
#print axioms listPositiveCount_centreQuotientList

end JSP000404Research
