import JSP000404Research.CentreQuotientData
import JSP000404Research.SupportListBridge
import JSP000404Research.SupportTwoDeletion
import Mathlib.Data.List.OfFn
import Mathlib.Tactic

/-!
# Function-valued quotient data and the concrete centre exponent

The transition modules prefer quotient lists, while the Sendov exponent
arithmetic uses a finite function q : Fin m -> Nat.

For a concrete centre cycle C we therefore define

  centreQuotient C t r = floor(t * C.gaps.get r).

Its List.ofFn representation is exactly quotientList t C.gaps, so all list and
function statements refer to one object.

The centre exponent is then the genuine

  k(C,t) = floorExcess (centreQuotient C t).

In the delta<1 range its quotient mass is at most n.  Therefore, once the
geometric sign path is proved to change only across positive quotients, every
centre with k >= n-2 has a unique transition carried by a positive gap.
-/

namespace JSP000404Research

open scoped BigOperators

def centreQuotient
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane} {hp : Function.Injective p} {i : V}
    (C : CentreProjectiveCycle hp i)
    (t : ℝ) :
    Fin C.gaps.length → ℕ :=
  fun r => Nat.floor (t * C.gaps.get r)

theorem centreQuotient_ofFn
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane} {hp : Function.Injective p} {i : V}
    (C : CentreProjectiveCycle hp i)
    (t : ℝ) :
    List.ofFn (centreQuotient C t) =
      quotientList t C.gaps := by
  apply List.ext_get
  · simp [centreQuotient, quotientList]
  · intro n hleft hright
    simp [centreQuotient, quotientList]

theorem centreQuotient_sum_eq_list_sum
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane} {hp : Function.Injective p} {i : V}
    (C : CentreProjectiveCycle hp i)
    (t : ℝ) :
    (∑ r, centreQuotient C t r) =
      (quotientList t C.gaps).sum := by
  rw [← List.sum_ofFn, centreQuotient_ofFn]

/-- List exponent of the canonical List.ofFn representation is exactly the
finite-function floor excess. -/
theorem listExponent_ofFn_eq_floorExcess
    {m : ℕ} (q : Fin m → ℕ) :
    listExponent (List.ofFn q) = floorExcess q := by
  induction m with
  | zero =>
      simp [listExponent, floorExcess]
  | succ m ih =>
      rw [List.ofFn_succ]
      unfold listExponent floorExcess
      rw [List.map_cons, List.sum_cons, Fin.sum_univ_succ]
      have htail :=
        ih (fun i : Fin m => q i.succ)
      unfold listExponent floorExcess at htail
      simpa [excess] using congrArg id htail

/-- Concrete quotient-list exponent equals the centre floor-excess exponent. -/
theorem listExponent_quotientList_eq_centreExponent
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane} {hp : Function.Injective p} {i : V}
    (C : CentreProjectiveCycle hp i)
    (t : ℝ) :
    listExponent (quotientList t C.gaps) =
      floorExcess (centreQuotient C t) := by
  rw [← centreQuotient_ofFn]
  exact listExponent_ofFn_eq_floorExcess
    (centreQuotient C t)


/-- Concrete Sendov exponent of one centre. -/
def centreExponent
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane} {hp : Function.Injective p} {i : V}
    (C : CentreProjectiveCycle hp i)
    (t : ℝ) : ℕ :=
  floorExcess (centreQuotient C t)


@[simp] theorem listExponent_quotientList_eq_centreExponent'
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane} {hp : Function.Injective p} {i : V}
    (C : CentreProjectiveCycle hp i)
    (t : ℝ) :
    listExponent (quotientList t C.gaps) =
      centreExponent C t := by
  unfold centreExponent
  exact listExponent_quotientList_eq_centreExponent C t

/-- Concrete Sendov deficit at integer level n. -/
def centreDeficit
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane} {hp : Function.Injective p} {i : V}
    (C : CentreProjectiveCycle hp i)
    (t : ℝ) (n : ℕ) : ℕ :=
  n - centreExponent C t

theorem centreQuotient_function_sum_le_n
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane} {hp : Function.Injective p} {i : V}
    (C : CentreProjectiveCycle hp i)
    (n : ℕ) (delta t : ℝ)
    (hn : 1 ≤ n)
    (hdelta0 : 0 ≤ delta)
    (hdelta1 : delta < 1)
    (ht : t = (n : ℝ) + delta) :
    (∑ r, centreQuotient C t r) ≤ n := by
  rw [centreQuotient_sum_eq_list_sum]
  exact centreQuotient_sum_le_n
    C n delta t hn hdelta0 hdelta1 ht

/-- Large exponent gives the support<=2 regime for the actual centre
quotient function. -/
theorem centre_positiveSupport_le_two_of_large_exponent
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane} {hp : Function.Injective p} {i : V}
    (C : CentreProjectiveCycle hp i)
    (n : ℕ) (delta t : ℝ)
    (hn : 1 ≤ n)
    (hdelta0 : 0 ≤ delta)
    (hdelta1 : delta < 1)
    (ht : t = (n : ℝ) + delta)
    (hlarge : n - 2 ≤ centreExponent C t) :
    positiveSupport (centreQuotient C t) ≤ 2 := by
  apply positiveSupport_le_two_of_exponent_ge_n_sub_two
    (centreQuotient C t) n
  · exact centreQuotient_function_sum_le_n
      C n delta t hn hdelta0 hdelta1 ht
  · simpa [centreExponent] using hlarge
  · exact (floorExcess_le_sum (centreQuotient C t)).trans
      (centreQuotient_function_sum_le_n
        C n delta t hn hdelta0 hdelta1 ht)

/-- Concrete high-exponent transition theorem, conditional only on the
geometric sign-change rule and antiperiodic endpoint. -/
theorem centre_large_exponent_has_positive_transition_gap
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane} {hp : Function.Injective p} {i : V}
    (C : CentreProjectiveCycle hp i)
    (n : ℕ) (delta t : ℝ)
    (hn : 1 ≤ n)
    (hdelta0 : 0 ≤ delta)
    (hdelta1 : delta < 1)
    (ht : t = (n : ℝ) + delta)
    (hlarge : n - 2 ≤ centreExponent C t)
    (a : Bool) (signPath : List Bool)
    (hchanges :
      ChangesOnlyOnPositive
        a signPath (quotientList t C.gaps))
    (hlast :
      boolLastFrom a signPath = !a) :
    ∃ pre post : List ℕ, ∃ qe : ℕ,
      qe ≠ 0 ∧
      quotientList t C.gaps =
        pre ++ qe :: post ∧
      signPath =
        List.replicate pre.length a ++
          List.replicate (post.length + 1) (!a) := by
  have hsupportList :
      listPositiveCount (quotientList t C.gaps) ≤ 2 := by
    rw [← centreQuotient_ofFn]
    rw [listPositiveCount_ofFn_eq_positiveSupport]
    exact centre_positiveSupport_le_two_of_large_exponent
      C n delta t hn hdelta0 hdelta1 ht hlarge
  exact antiperiodic_positive_transition_gap_of_support_le_two
    a signPath (quotientList t C.gaps)
    hchanges hlast hsupportList

#print axioms centreQuotient_ofFn
#print axioms centreQuotient_function_sum_le_n
#print axioms centre_positiveSupport_le_two_of_large_exponent
#print axioms centre_large_exponent_has_positive_transition_gap

end JSP000404Research
