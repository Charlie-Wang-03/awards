import JSP000404Research.BoundaryFailureStructure
import Mathlib.Tactic

/-!
# Support distribution at a local phase-budget failure

Let q be the geometric quotient vector and b the phase-boundary count vector.
Under one-exception domination, a strict local budget failure has exact
floor-excess loss one.

There is a second exact consequence which is especially useful geometrically.
Write

  d = n - sum q.

Every q-positive gap is still hit by at least one phase boundary: regular
positive gaps satisfy q i <= b i, and the exceptional gap satisfies
q e = b e + 1 with b e >= 1.

Hence the support of b consists of

* all positive q-gaps, plus
* some zero q-gaps.

The zero-carry identities then force the number of hit zero q-gaps to be
exactly

  d + 1.

This is the compensating boundary distribution behind a bad phase: one
boundary is lost from the exceptional positive gap, while d+1 zero gaps are
hit.
-/

namespace JSP000404Research

open scoped BigOperators

/-- Number of q-zero gaps which nevertheless contain at least one phase
boundary. -/
def zeroHitSupport
    {I : Type*} [Fintype I]
    (q b : I → ℕ) : ℕ :=
  ∑ i, if q i = 0 ∧ b i ≠ 0 then 1 else 0

/-- If every q-positive coordinate stays b-positive, then b-support splits
into the original q-support plus the hit zero gaps. -/
theorem positiveSupport_eq_add_zeroHitSupport
    {I : Type*} [Fintype I]
    (q b : I → ℕ)
    (hpres : ∀ i, q i ≠ 0 → b i ≠ 0) :
    positiveSupport b =
      positiveSupport q + zeroHitSupport q b := by
  classical
  unfold positiveSupport zeroHitSupport
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hq : q i = 0
  · by_cases hb : b i = 0 <;> simp [hq, hb]
  · have hb : b i ≠ 0 := hpres i hq
    simp [hq, hb]

/-- Under a genuine one-exception budget failure, every positive q-gap still
contains at least one phase boundary. -/
theorem positive_gap_preserved_of_budget_failure
    {I : Type*} [Fintype I]
    (q b : I → ℕ) (e : I) (n : ℕ)
    (hsum : (∑ i, b i) = n)
    (hregular : ∀ i, i ≠ e → q i ≤ b i)
    (hexception : q e ≤ b e + 1)
    (hbad : n - floorExcess q < positiveSupport b) :
    ∀ i, q i ≠ 0 → b i ≠ 0 := by
  intro i hqi
  by_cases hie : i = e
  · subst i
    have hbpos :=
      exceptional_boundary_pos_of_budget_failure
        q b e n hsum hregular hexception hbad
    omega
  · have hle := hregular i hie
    omega

/-- Exact count of boundary-hit zero gaps at a bad phase.

The hypothesis sum q <= n is the usual Sendov floor-defect condition.
-/
theorem zeroHitSupport_eq_floorDefect_add_one_of_budget_failure
    {I : Type*} [Fintype I]
    (q b : I → ℕ) (e : I) (n : ℕ)
    (hsum : (∑ i, b i) = n)
    (hQ : (∑ i, q i) ≤ n)
    (hregular : ∀ i, i ≠ e → q i ≤ b i)
    (hexception : q e ≤ b e + 1)
    (hbad : n - floorExcess q < positiveSupport b) :
    zeroHitSupport q b = (n - ∑ i, q i) + 1 := by
  have hpres :=
    positive_gap_preserved_of_budget_failure
      q b e n hsum hregular hexception hbad
  have hsplit :=
    positiveSupport_eq_add_zeroHitSupport q b hpres
  have hqID := floorExcess_add_positiveSupport q
  have hbID := floorExcess_add_positiveSupport b
  have hexact :=
    floorExcess_eq_add_one_of_budget_failure
      q b e n hsum hregular hexception hbad
  rw [hsum] at hbID
  omega

/-- Rewriting the same count using the Sendov deficit decomposition:
zero-hit count = ell - positiveSupport q + 1. -/
theorem zeroHitSupport_eq_deficit_sub_support_add_one
    {I : Type*} [Fintype I]
    (q b : I → ℕ) (e : I) (n ell : ℕ)
    (hsum : (∑ i, b i) = n)
    (hQ : (∑ i, q i) ≤ n)
    (hell : ell = n - floorExcess q)
    (hregular : ∀ i, i ≠ e → q i ≤ b i)
    (hexception : q e ≤ b e + 1)
    (hbad : n - floorExcess q < positiveSupport b) :
    zeroHitSupport q b =
      (ell - positiveSupport q) + 1 := by
  have hz :=
    zeroHitSupport_eq_floorDefect_add_one_of_budget_failure
      q b e n hsum hQ hregular hexception hbad
  have hdec :=
    deficit_eq_floorDefect_add_support q n hQ
  rw [hell] at hdec
  omega

#print axioms positiveSupport_eq_add_zeroHitSupport
#print axioms positive_gap_preserved_of_budget_failure
#print axioms zeroHitSupport_eq_floorDefect_add_one_of_budget_failure
#print axioms zeroHitSupport_eq_deficit_sub_support_add_one

end JSP000404Research
