
import JSP000404Research.StandardResidualBoundaryBudget
import JSP000404Research.BoundaryExcessBalance
import Mathlib.Tactic

/-!
# Exact arithmetic structure of a standard-residual one-layer loss

The standard residual partition has n+1 boundary points.  Let q be the natural
Sendov quotient vector at one centre and b the allocation of those n+1
boundaries among its cyclic ray gaps.

Assume full domination q(i) <= b(i), and suppose the one-layer support bound
is saturated:

  positiveSupport(b) = n - floorExcess(q) + 1.

Then the floor-excess comparison is itself an equality.  Since q<=b
coordinatewise, equality of the total floor excess forces equality at every
coordinate.

Consequences:

* every positive quotient gap is hit exactly minimally: b(i)=q(i);
* every zero quotient gap receives at most one boundary;
* all n+1-sum(q) extra boundaries are exactly the zero-gap hits.

If sum(q)<=n, the zero-hit count is therefore

  (n-sum(q))+1.

So an exact projected one-layer loss has a rigid interpretation: compared with
the ordinary n-boundary floor defect, exactly one additional zero quotient gap
is hit.
-/

namespace JSP000404Research

open scoped BigOperators

theorem standardResidual_floorExcess_eq_of_exact_oneLayer_support
    {I : Type*} [Fintype I]
    (q b : I → ℕ) (n : ℕ)
    (hk : floorExcess q ≤ n)
    (hsumB : (∑ i, b i) = n + 1)
    (hloss :
      positiveSupport b = n - floorExcess q + 1) :
    floorExcess b = floorExcess q := by
  have hbID := floorExcess_add_positiveSupport b
  rw [hsumB, hloss] at hbID
  omega

theorem standardResidual_pointwise_excess_eq_of_exact_oneLayer_support
    {I : Type*} [Fintype I]
    (q b : I → ℕ) (n : ℕ)
    (hk : floorExcess q ≤ n)
    (hsumB : (∑ i, b i) = n + 1)
    (hdom : ∀ i, q i ≤ b i)
    (hloss :
      positiveSupport b = n - floorExcess q + 1) :
    ∀ i, q i - 1 = b i - 1 := by
  intro i
  have hEq :=
    standardResidual_floorExcess_eq_of_exact_oneLayer_support
      q b n hk hsumB hloss
  have hle :
      ∀ j : I, q j - 1 ≤ b j - 1 := by
    intro j
    omega
  by_contra hne
  have hlt :
      q i - 1 < b i - 1 := by
    have hi := hle i
    omega
  have hsumlt :
      floorExcess q < floorExcess b := by
    unfold floorExcess
    exact Finset.sum_lt_sum
      (fun j _ => hle j)
      ⟨i, Finset.mem_univ i, hlt⟩
  omega

/-- Positive quotient coordinates are matched exactly. -/
theorem standardResidual_boundary_eq_quotient_of_positive
    {I : Type*} [Fintype I]
    (q b : I → ℕ) (n : ℕ)
    (hk : floorExcess q ≤ n)
    (hsumB : (∑ i, b i) = n + 1)
    (hdom : ∀ i, q i ≤ b i)
    (hloss :
      positiveSupport b = n - floorExcess q + 1)
    (i : I)
    (hqi : q i ≠ 0) :
    b i = q i := by
  have hEx :=
    standardResidual_pointwise_excess_eq_of_exact_oneLayer_support
      q b n hk hsumB hdom hloss i
  have hpos : 1 ≤ q i :=
    Nat.one_le_iff_ne_zero.mpr hqi
  have hle := hdom i
  omega

/-- Zero quotient coordinates can receive at most one standard-residual
boundary. -/
theorem standardResidual_boundary_le_one_of_zero
    {I : Type*} [Fintype I]
    (q b : I → ℕ) (n : ℕ)
    (hk : floorExcess q ≤ n)
    (hsumB : (∑ i, b i) = n + 1)
    (hdom : ∀ i, q i ≤ b i)
    (hloss :
      positiveSupport b = n - floorExcess q + 1)
    (i : I)
    (hqi : q i = 0) :
    b i ≤ 1 := by
  have hEx :=
    standardResidual_pointwise_excess_eq_of_exact_oneLayer_support
      q b n hk hsumB hdom hloss i
  rw [hqi] at hEx
  omega

/-- Every positive quotient gap remains boundary-positive. -/
theorem standardResidual_positive_preserved
    {I : Type*} [Fintype I]
    (q b : I → ℕ)
    (hdom : ∀ i, q i ≤ b i) :
    ∀ i, q i ≠ 0 → b i ≠ 0 := by
  intro i hqi hbi
  have hle := hdom i
  rw [hbi] at hle
  omega

/-- Exact count of zero quotient gaps hit by the n+1 standard-residual
boundaries in the one-layer saturation case. -/
theorem standardResidual_zeroHitSupport_eq_floorDefect_add_one
    {I : Type*} [Fintype I]
    (q b : I → ℕ) (n : ℕ)
    (hQ : (∑ i, q i) ≤ n)
    (hsumB : (∑ i, b i) = n + 1)
    (hdom : ∀ i, q i ≤ b i)
    (hloss :
      positiveSupport b = n - floorExcess q + 1) :
    zeroHitSupport q b = (n - ∑ i, q i) + 1 := by
  have hk :
      floorExcess q ≤ n :=
    (floorExcess_le_sum q).trans hQ
  have hEq :=
    standardResidual_floorExcess_eq_of_exact_oneLayer_support
      q b n hk hsumB hloss
  have hpres :=
    standardResidual_positive_preserved q b hdom
  have hQsucc :
      (∑ i, q i) ≤ n + 1 := by
    omega
  have hbal :=
    boundary_excess_add_zeroHits_eq
      q b (n + 1) hsumB hQsucc hpres
  rw [hEq] at hbal
  omega

/-- Complete rigid pointwise structure. -/
theorem standardResidual_exact_oneLayer_structure
    {I : Type*} [Fintype I]
    (q b : I → ℕ) (n : ℕ)
    (hQ : (∑ i, q i) ≤ n)
    (hsumB : (∑ i, b i) = n + 1)
    (hdom : ∀ i, q i ≤ b i)
    (hloss :
      positiveSupport b = n - floorExcess q + 1) :
    (∀ i, q i ≠ 0 → b i = q i) ∧
    (∀ i, q i = 0 → b i ≤ 1) ∧
    zeroHitSupport q b = (n - ∑ i, q i) + 1 := by
  have hk :
      floorExcess q ≤ n :=
    (floorExcess_le_sum q).trans hQ
  refine ⟨?_, ?_, ?_⟩
  · intro i hqi
    exact standardResidual_boundary_eq_quotient_of_positive
      q b n hk hsumB hdom hloss i hqi
  · intro i hqi
    exact standardResidual_boundary_le_one_of_zero
      q b n hk hsumB hdom hloss i hqi
  · exact standardResidual_zeroHitSupport_eq_floorDefect_add_one
      q b n hQ hsumB hdom hloss

#print axioms standardResidual_floorExcess_eq_of_exact_oneLayer_support
#print axioms standardResidual_pointwise_excess_eq_of_exact_oneLayer_support
#print axioms standardResidual_boundary_eq_quotient_of_positive
#print axioms standardResidual_boundary_le_one_of_zero
#print axioms standardResidual_zeroHitSupport_eq_floorDefect_add_one
#print axioms standardResidual_exact_oneLayer_structure

end JSP000404Research
