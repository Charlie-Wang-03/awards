import JSP000404Research.CentreExponent
import JSP000404Research.SixPointThirdLayerTerminal
import Mathlib.Tactic

/-!
# Unit-quotient budget in the six-point third-layer terminal

Terminal critical transition gaps in the lower branch have quotient exactly 1.
Thus it is useful to count unit quotient coordinates directly, rather than all
global edge directions.

For a quotient vector q define

  unitSupport q = #{i | q i = 1}.

If floorExcess q is positive, at least one positive coordinate is >=2.
Therefore

  unitSupport q + 1 <= positiveSupport q.

Consequences in the six-point 1+5 terminal:

* the unique top centre k=n-1 has positive support at most one and positive
  floor excess, so it has no unit quotient;
* every minimum centre k=n-3 has support at most three and positive floor
  excess, so it has at most two unit quotients.

Hence the total number of unit quotient coordinates over all six centres is
at most 10.
-/

namespace JSP000404Research

open scoped BigOperators

def unitSupport
    {I : Type*} [Fintype I]
    (q : I → ℕ) : ℕ :=
  ∑ i, if q i = 1 then 1 else 0

def nonUnitPositiveSupport
    {I : Type*} [Fintype I]
    (q : I → ℕ) : ℕ :=
  ∑ i, if 2 ≤ q i then 1 else 0

theorem positiveSupport_eq_unit_add_nonUnit
    {I : Type*} [Fintype I]
    (q : I → ℕ) :
    positiveSupport q =
      unitSupport q + nonUnitPositiveSupport q := by
  classical
  unfold positiveSupport unitSupport nonUnitPositiveSupport
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  by_cases h0 : q i = 0
  · simp [h0]
  · by_cases h1 : q i = 1
    · simp [h0, h1]
    · have h2 : 2 ≤ q i := by omega
      simp [h0, h1, h2]

theorem nonUnitPositiveSupport_pos_of_floorExcess_pos
    {I : Type*} [Fintype I]
    (q : I → ℕ)
    (hex : 1 ≤ floorExcess q) :
    1 ≤ nonUnitPositiveSupport q := by
  classical
  by_contra hnot
  have hz : nonUnitPositiveSupport q = 0 := by omega
  have hall : ∀ i : I, q i ≤ 1 := by
    intro i
    by_contra hi
    have hi2 : 2 ≤ q i := by omega
    unfold nonUnitPositiveSupport at hz
    have hsingle :
        (if 2 ≤ q i then 1 else 0) ≤
          ∑ j : I, (if 2 ≤ q j then 1 else 0) := by
      exact Finset.single_le_sum
        (fun _ _ => Nat.zero_le _)
        (Finset.mem_univ i)
    simp [hi2, hz] at hsingle
  have hex0 : floorExcess q = 0 := by
    unfold floorExcess
    apply Finset.sum_eq_zero
    intro i _
    have hi := hall i
    omega
  omega

theorem unitSupport_add_one_le_positiveSupport_of_floorExcess_pos
    {I : Type*} [Fintype I]
    (q : I → ℕ)
    (hex : 1 ≤ floorExcess q) :
    unitSupport q + 1 ≤ positiveSupport q := by
  rw [positiveSupport_eq_unit_add_nonUnit q]
  have hpos :=
    nonUnitPositiveSupport_pos_of_floorExcess_pos q hex
  omega

theorem unitSupport_le_two_of_floorExcess_pos_support_le_three
    {I : Type*} [Fintype I]
    (q : I → ℕ)
    (hex : 1 ≤ floorExcess q)
    (hsupport : positiveSupport q ≤ 3) :
    unitSupport q ≤ 2 := by
  have h :=
    unitSupport_add_one_le_positiveSupport_of_floorExcess_pos
      q hex
  omega

theorem centre_unitSupport_le_two_of_exponent_n_sub_three
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane} {hp : Function.Injective p}
    {i : V}
    (C : CentreProjectiveCycle hp i)
    {t delta : ℝ} {n : ℕ}
    (hn : 4 ≤ n)
    (hdelta0 : 0 ≤ delta)
    (hdelta1 : delta < 1)
    (ht : t = (n : ℝ) + delta)
    (hexp : centreExponent C t = n - 3) :
    unitSupport (centreQuotient C t) ≤ 2 := by
  have hsum :=
    centreQuotient_function_sum_le_n
      C n delta t (by omega) hdelta0 hdelta1 ht
  have hsupport :
      positiveSupport (centreQuotient C t) ≤ 3 := by
    have h :=
      positiveSupport_le_deficit
        (centreQuotient C t) n hsum
    rw [← show floorExcess (centreQuotient C t) =
        centreExponent C t by rfl, hexp] at h
    omega
  have hexcess :
      1 ≤ floorExcess (centreQuotient C t) := by
    change 1 ≤ centreExponent C t
    rw [hexp]
    omega
  exact unitSupport_le_two_of_floorExcess_pos_support_le_three
    (centreQuotient C t) hexcess hsupport

theorem centre_unitSupport_eq_zero_of_exponent_n_sub_one
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane} {hp : Function.Injective p}
    {i : V}
    (C : CentreProjectiveCycle hp i)
    {t delta : ℝ} {n : ℕ}
    (hn : 4 ≤ n)
    (hdelta0 : 0 ≤ delta)
    (hdelta1 : delta < 1)
    (ht : t = (n : ℝ) + delta)
    (hexp : centreExponent C t = n - 1) :
    unitSupport (centreQuotient C t) = 0 := by
  have hsum :=
    centreQuotient_function_sum_le_n
      C n delta t (by omega) hdelta0 hdelta1 ht
  have hsupport :
      positiveSupport (centreQuotient C t) ≤ 1 := by
    have h :=
      positiveSupport_le_deficit
        (centreQuotient C t) n hsum
    rw [← show floorExcess (centreQuotient C t) =
        centreExponent C t by rfl, hexp] at h
    omega
  have hexcess :
      1 ≤ floorExcess (centreQuotient C t) := by
    change 1 ≤ centreExponent C t
    rw [hexp]
    omega
  have hunit :=
    unitSupport_add_one_le_positiveSupport_of_floorExcess_pos
      (centreQuotient C t) hexcess
  omega

/-- Global unit-slot budget for the six-point top + five n-3 profile. -/
theorem six_point_top_five_minima_unitSupport_sum_le_ten
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane} {hp : Function.Injective p}
    (C : ∀ i : V, CentreProjectiveCycle hp i)
    {t delta : ℝ} {n : ℕ}
    (hn : 4 ≤ n)
    (hdelta0 : 0 ≤ delta)
    (hdelta1 : delta < 1)
    (ht : t = (n : ℝ) + delta)
    (hcard : Fintype.card V = 6)
    (s : V)
    (hTop : centreExponent (C s) t = n - 1)
    (hMin :
      ∀ i : V, i ≠ s →
        centreExponent (C i) t = n - 3) :
    (∑ i : V, unitSupport (centreQuotient (C i) t)) ≤ 10 := by
  classical
  have hs0 :
      unitSupport (centreQuotient (C s) t) = 0 :=
    centre_unitSupport_eq_zero_of_exponent_n_sub_one
      (C s) hn hdelta0 hdelta1 ht hTop
  have hother :
      ∀ i : V, i ≠ s →
        unitSupport (centreQuotient (C i) t) ≤ 2 := by
    intro i his
    exact centre_unitSupport_le_two_of_exponent_n_sub_three
      (C i) hn hdelta0 hdelta1 ht (hMin i his)
  calc
    (∑ i : V, unitSupport (centreQuotient (C i) t))
        =
      unitSupport (centreQuotient (C s) t) +
        ∑ i ∈ (Finset.univ.erase s),
          unitSupport (centreQuotient (C i) t) := by
            rw [← Finset.sum_erase_add _ _ (Finset.mem_univ s)]
            simp [add_comm]
    _ =
      ∑ i ∈ (Finset.univ.erase s),
        unitSupport (centreQuotient (C i) t) := by
          rw [hs0, zero_add]
    _ ≤ ∑ _i ∈ (Finset.univ.erase s), 2 := by
          apply Finset.sum_le_sum
          intro i hi
          have his : i ≠ s := by
            exact (Finset.mem_erase.mp hi).1
          exact hother i his
    _ = 2 * ((Finset.univ.erase s).card) := by
          simp [Nat.mul_comm]
    _ = 10 := by
          rw [Finset.card_erase_of_mem (Finset.mem_univ s)]
          simp [hcard]

#print axioms positiveSupport_eq_unit_add_nonUnit
#print axioms unitSupport_add_one_le_positiveSupport_of_floorExcess_pos
#print axioms centre_unitSupport_le_two_of_exponent_n_sub_three
#print axioms centre_unitSupport_eq_zero_of_exponent_n_sub_one
#print axioms six_point_top_five_minima_unitSupport_sum_le_ten

end JSP000404Research
