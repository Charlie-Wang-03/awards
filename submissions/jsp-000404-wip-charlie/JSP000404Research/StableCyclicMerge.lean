import JSP000404Research.StableCyclicSupport
import JSP000404Research.MergeZeroGain
import JSP000404Research.CentreExponent
import Mathlib.Tactic

/-!
# From cyclic zero-gain merges to separated positive support

A concrete deletion-stable centre is expected to have one actual binary carry
for every incident-ray deletion.  At the arithmetic level, all we need here is
that every cyclic adjacent quotient pair admits a merge with zero exponent
gain.

The carry value is irrelevant for the first conclusion: zero gain itself
forbids two positive adjacent quotients.  Hence every positive position is
followed cyclically by a zero position, and the independent-support bound from
StableCyclicSupport applies.

This file packages that reusable arithmetic interface.
-/

namespace JSP000404Research

/-- Arithmetic cyclic merge stability: for each adjacent cyclic pair, one
specified carry gives zero exponent gain. -/
def CyclicMergeStable
    {m : ℕ}
    (q : Fin m → ℕ)
    (carry : Fin m → ℕ) : Prop :=
  ∀ i,
    exponentAfterMerge 0
        (q i) (q (finRotate m i)) (carry i) =
      exponentBeforeMerge 0
        (q i) (q (finRotate m i))

/-- Zero-gain cyclic merges force separated positive support, independently of
the carry values. -/
theorem cyclicSeparatedPositive_of_cyclicMergeStable
    {m : ℕ}
    (q : Fin m → ℕ)
    (carry : Fin m → ℕ)
    (hstable : CyclicMergeStable q carry) :
    CyclicSeparatedPositive q := by
  intro i hi
  by_contra hnext
  have hzero := hstable i
  have hnotBoth :=
    zero_gain_not_both_pos hzero
  apply hnotBoth
  constructor
  · exact Nat.one_le_iff_ne_zero.mpr hi
  · exact Nat.one_le_iff_ne_zero.mpr hnext

/-- Therefore every cyclically zero-gain quotient profile has support at most
half the cycle length. -/
theorem positiveSupport_mul_two_le_of_cyclicMergeStable
    {m : ℕ}
    (q : Fin m → ℕ)
    (carry : Fin m → ℕ)
    (hstable : CyclicMergeStable q carry) :
    2 * positiveSupport q ≤ m := by
  exact positiveSupport_mul_two_le_length_of_cyclicSeparated
    q
    (cyclicSeparatedPositive_of_cyclicMergeStable
      q carry hstable)

/-- Half-length version. -/
theorem positiveSupport_le_half_of_cyclicMergeStable
    {m : ℕ}
    (q : Fin m → ℕ)
    (carry : Fin m → ℕ)
    (hstable : CyclicMergeStable q carry) :
    positiveSupport q ≤ m / 2 := by
  exact positiveSupport_le_half_length_of_cyclicSeparated
    q
    (cyclicSeparatedPositive_of_cyclicMergeStable
      q carry hstable)

/-- Concrete-centre specialization at the quotient-function level. -/
theorem centre_positiveSupport_mul_two_le_of_cyclicMergeStable
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane} {hp : Function.Injective p} {i : V}
    (C : CentreProjectiveCycle hp i)
    (t : ℝ)
    (carry : Fin C.gaps.length → ℕ)
    (hstable :
      CyclicMergeStable (centreQuotient C t) carry) :
    2 * positiveSupport (centreQuotient C t) ≤
      C.gaps.length := by
  exact positiveSupport_mul_two_le_of_cyclicMergeStable
    (centreQuotient C t) carry hstable

/-- Stable concrete quotient profiles retain the usual Sendov exponent/support
budget, now together with the independent-set support restriction. -/
theorem centre_stable_support_and_exponent_budget
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane} {hp : Function.Injective p} {i : V}
    (C : CentreProjectiveCycle hp i)
    {n : ℕ} {delta t : ℝ}
    (hn : 1 ≤ n)
    (hdelta0 : 0 ≤ delta)
    (hdelta1 : delta < 1)
    (ht : t = (n : ℝ) + delta)
    (carry : Fin C.gaps.length → ℕ)
    (hstable :
      CyclicMergeStable (centreQuotient C t) carry) :
    2 * positiveSupport (centreQuotient C t) ≤
        C.gaps.length
      ∧
    centreExponent C t +
        positiveSupport (centreQuotient C t) ≤ n := by
  constructor
  · exact centre_positiveSupport_mul_two_le_of_cyclicMergeStable
      C t carry hstable
  · unfold centreExponent
    rw [floorExcess_add_positiveSupport]
    exact centreQuotient_function_sum_le_n
      C n delta t hn hdelta0 hdelta1 ht

#print axioms cyclicSeparatedPositive_of_cyclicMergeStable
#print axioms positiveSupport_mul_two_le_of_cyclicMergeStable
#print axioms centre_positiveSupport_mul_two_le_of_cyclicMergeStable
#print axioms centre_stable_support_and_exponent_budget

end JSP000404Research
