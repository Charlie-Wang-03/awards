import JSP000404Research.ThreeRayCentreData
import JSP000404Research.DeficitTwo
import JSP000404Research.SupportListBridge
import Mathlib.Tactic

/-!
# The unique zero gap in a four-point deficit-two/support-two centre

For a four-point centre there are exactly three cyclic projective gaps.  In the
deficit-two/support-two regime,

  centreExponent = n-2,
  positiveSupport = 2.

Using floorExcess + positiveSupport = total quotient mass, the three quotient
entries sum exactly to n.  Since exactly two are positive, exactly one is zero.

Because the three scaled gaps sum to

  t = n + delta,

while each positive floor quotient is bounded above by its scaled gap, the
unique zero gap has scaled width at most delta.

This is the precise remainder estimate used to turn the zero gap into a
delta*lambda-small genuine angle.
-/

namespace JSP000404Research

open Real
open scoped BigOperators

theorem three_positiveCount_two_exactly_one_zero
    {q0 q1 q2 : ℕ}
    (hsupport : listPositiveCount [q0,q1,q2] = 2) :
    (q0 = 0 ∧ q1 ≠ 0 ∧ q2 ≠ 0) ∨
    (q0 ≠ 0 ∧ q1 = 0 ∧ q2 ≠ 0) ∨
    (q0 ≠ 0 ∧ q1 ≠ 0 ∧ q2 = 0) := by
  by_cases h0 : q0 = 0 <;>
    by_cases h1 : q1 = 0 <;>
    by_cases h2 : q2 = 0 <;>
    simp [listPositiveCount, h0, h1, h2] at hsupport ⊢

theorem three_quotient_sum_eq_n_of_deficit_two_support_two
    {p : Fin 4 → Plane} {hp : Function.Injective p}
    {i : Fin 4}
    (C : CentreProjectiveCycle hp i)
    {t : ℝ} {n : ℕ}
    (hexp : centreExponent C t = n - 2)
    (hsupport :
      positiveSupport (centreQuotient C t) = 2) :
    (quotientList t C.gaps).sum = n := by
  have hid :=
    floorExcess_add_positiveSupport (centreQuotient C t)
  have hsum :
      ∑ r, centreQuotient C t r = n := by
    unfold centreExponent at hexp
    rw [hexp, hsupport] at hid
    omega
  rw [centreQuotient_sum_eq_list_sum C t] at hsum
  exact hsum

/-- Three explicit quotient entries sum to n. -/
theorem three_explicit_quotient_sum_eq_n_of_deficit_two_support_two
    {p : Fin 4 → Plane} {hp : Function.Injective p}
    {i : Fin 4}
    (C : CentreProjectiveCycle hp i)
    {t : ℝ} {n : ℕ}
    (r0 r1 r2 : OtherVertex i)
    (hrays : C.rays = [r0,r1,r2])
    (hexp : centreExponent C t = n - 2)
    (hsupport :
      positiveSupport (centreQuotient C t) = 2) :
    Nat.floor (t * gap01 r0 r1) +
      Nat.floor (t * gap12 r1 r2) +
      Nat.floor (t * gap20 r0 r2) = n := by
  have hsum :=
    three_quotient_sum_eq_n_of_deficit_two_support_two
      C hexp hsupport
  rw [centre_quotientList_eq_three C t r0 r1 r2 hrays] at hsum
  simpa [Nat.add_assoc] using hsum

/-- The concrete three-entry quotient list has positive count two. -/
theorem three_explicit_positiveCount_eq_two
    {p : Fin 4 → Plane} {hp : Function.Injective p}
    {i : Fin 4}
    (C : CentreProjectiveCycle hp i)
    {t : ℝ}
    (r0 r1 r2 : OtherVertex i)
    (hrays : C.rays = [r0,r1,r2])
    (hsupport :
      positiveSupport (centreQuotient C t) = 2) :
    listPositiveCount
      [Nat.floor (t * gap01 r0 r1),
       Nat.floor (t * gap12 r1 r2),
       Nat.floor (t * gap20 r0 r2)] = 2 := by
  have hlist :
      listPositiveCount (quotientList t C.gaps) = 2 := by
    rw [← centreQuotient_ofFn]
    rw [listPositiveCount_ofFn_eq_positiveSupport]
    exact hsupport
  rw [centre_quotientList_eq_three C t r0 r1 r2 hrays] at hlist
  exact hlist

private theorem zero_scaled_of_three_floor_sum
    {x0 x1 x2 delta : ℝ} {n : ℕ}
    (hx0 : 0 ≤ x0) (hx1 : 0 ≤ x1) (hx2 : 0 ≤ x2)
    (hsumR : x0 + x1 + x2 = (n : ℝ) + delta)
    (hsumQ :
      Nat.floor x0 + Nat.floor x1 + Nat.floor x2 = n) :
    (Nat.floor x0 = 0 → x0 ≤ delta) ∧
    (Nat.floor x1 = 0 → x1 ≤ delta) ∧
    (Nat.floor x2 = 0 → x2 ≤ delta) := by
  have hf0 : ((Nat.floor x0 : ℕ) : ℝ) ≤ x0 := Nat.floor_le hx0
  have hf1 : ((Nat.floor x1 : ℕ) : ℝ) ≤ x1 := Nat.floor_le hx1
  have hf2 : ((Nat.floor x2 : ℕ) : ℝ) ≤ x2 := Nat.floor_le hx2
  constructor
  · intro h0
    have h12 : Nat.floor x1 + Nat.floor x2 = n := by omega
    have hcast :
        (n : ℝ) =
          (Nat.floor x1 : ℝ) + (Nat.floor x2 : ℝ) := by
      exact_mod_cast h12.symm
    linarith
  constructor
  · intro h1
    have h02 : Nat.floor x0 + Nat.floor x2 = n := by omega
    have hcast :
        (n : ℝ) =
          (Nat.floor x0 : ℝ) + (Nat.floor x2 : ℝ) := by
      exact_mod_cast h02.symm
    linarith
  · intro h2
    have h01 : Nat.floor x0 + Nat.floor x1 = n := by omega
    have hcast :
        (n : ℝ) =
          (Nat.floor x0 : ℝ) + (Nat.floor x1 : ℝ) := by
      exact_mod_cast h01.symm
    linarith

/-- In the explicit three-ray cycle, whichever quotient is zero has scaled gap
at most delta. -/
theorem zero_gap_scaled_le_delta_of_deficit_two_support_two
    {p : Fin 4 → Plane} {hp : Function.Injective p}
    {i : Fin 4}
    (C : CentreProjectiveCycle hp i)
    {t delta : ℝ} {n : ℕ}
    (ht : t = (n : ℝ) + delta)
    (ht0 : 0 ≤ t)
    (r0 r1 r2 : OtherVertex i)
    (hrays : C.rays = [r0,r1,r2])
    (hexp : centreExponent C t = n - 2)
    (hsupport :
      positiveSupport (centreQuotient C t) = 2) :
    (Nat.floor (t * gap01 r0 r1) = 0 →
      t * gap01 r0 r1 ≤ delta) ∧
    (Nat.floor (t * gap12 r1 r2) = 0 →
      t * gap12 r1 r2 ≤ delta) ∧
    (Nat.floor (t * gap20 r0 r2) = 0 →
      t * gap20 r0 r2 ≤ delta) := by
  have hg := three_gaps_nonneg C r0 r1 r2 hrays
  have hx0 : 0 ≤ t * gap01 r0 r1 := mul_nonneg ht0 hg.1
  have hx1 : 0 ≤ t * gap12 r1 r2 := mul_nonneg ht0 hg.2.1
  have hx2 : 0 ≤ t * gap20 r0 r2 := mul_nonneg ht0 hg.2.2
  have hsumR := scaled_three_gaps_sum_t C t r0 r1 r2 hrays
  rw [ht] at hsumR
  have hsumQ :=
    three_explicit_quotient_sum_eq_n_of_deficit_two_support_two
      C r0 r1 r2 hrays hexp hsupport
  exact zero_scaled_of_three_floor_sum
    hx0 hx1 hx2 hsumR hsumQ

/-- There is exactly one zero quotient among the three explicit gaps. -/
theorem deficit_two_support_two_exactly_one_zero_gap
    {p : Fin 4 → Plane} {hp : Function.Injective p}
    {i : Fin 4}
    (C : CentreProjectiveCycle hp i)
    {t : ℝ}
    (r0 r1 r2 : OtherVertex i)
    (hrays : C.rays = [r0,r1,r2])
    (hsupport :
      positiveSupport (centreQuotient C t) = 2) :
    let q0 := Nat.floor (t * gap01 r0 r1)
    let q1 := Nat.floor (t * gap12 r1 r2)
    let q2 := Nat.floor (t * gap20 r0 r2)
    (q0 = 0 ∧ q1 ≠ 0 ∧ q2 ≠ 0) ∨
    (q0 ≠ 0 ∧ q1 = 0 ∧ q2 ≠ 0) ∨
    (q0 ≠ 0 ∧ q1 ≠ 0 ∧ q2 = 0) := by
  dsimp
  apply three_positiveCount_two_exactly_one_zero
  exact three_explicit_positiveCount_eq_two
    C r0 r1 r2 hrays hsupport

#print axioms three_positiveCount_two_exactly_one_zero
#print axioms three_explicit_quotient_sum_eq_n_of_deficit_two_support_two
#print axioms zero_gap_scaled_le_delta_of_deficit_two_support_two
#print axioms deficit_two_support_two_exactly_one_zero_gap

end JSP000404Research
