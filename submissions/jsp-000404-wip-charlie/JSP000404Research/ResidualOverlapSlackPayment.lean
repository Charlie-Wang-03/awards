
import JSP000404Research.ResidualSliceAccounting
import JSP000404Research.WeightedProfileRepair
import Mathlib.Tactic

/-!
# Strict projected slack pays all residual overlap

Let nu(v)=projectedFree(C,v).

Suppose every residual-active vertex satisfies one full projected slack layer

  exponent(v)+1 <= nu(v).

Then its dyadic profile surplus is at least half of its projected completion
cube:

  2^nu(v) <= 2 * (2^nu(v)-2^exponent(v)).

The residual-active cubes split into the two canonical residual-bit slices.
Cubes are pairwise disjoint inside each slice, and projected overlap is exactly
the intersection A0 inter A1 of the two slice unions.  Hence

  2*overlap <= card(A0)+card(A1).

Summing the half-cube surplus bound over both disjoint slices therefore gives

  overlapMass <= totalProfileSurplus.

Thus all projected overlap is automatically paid unless some overlap endpoint
is projected-saturated.
-/

namespace JSP000404Research
namespace OrderedEdgeColoring

open scoped BigOperators

theorem projectedCube_le_two_mul_surplus_of_strict
    {V : Type*} [LinearOrder V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (v : V)
    (hstrict :
      exponent v + 1 ≤ projectedFree C v) :
    2 ^ projectedFree C v ≤
      2 * dyadicProfileSurplus exponent (projectedFree C) v := by
  have hp :
      2 ^ (exponent v + 1) ≤
        2 ^ projectedFree C v :=
    Nat.pow_le_pow_right
      (by norm_num : 0 < 2) hstrict
  rw [pow_succ] at hp
  unfold dyadicProfileSurplus
  omega

theorem residualActiveSlice_disjoint
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1)) :
    Disjoint
      (residualActiveSlice C false)
      (residualActiveSlice C true) := by
  classical
  rw [Finset.disjoint_left]
  intro v hvFalse hvTrue
  have hf := (mem_residualActiveSlice C false v).1 hvFalse
  have ht := (mem_residualActiveSlice C true v).1 hvTrue
  rw [hf.2] at ht
  simp at ht

/-- The two slices are exactly the residual-active vertices. -/
theorem residualActiveSlice_union_eq
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1)) :
    residualActiveSlice C false ∪
      residualActiveSlice C true =
    (Finset.univ : Finset V).filter
      (fun v => residualCoord n ∈ active C v) := by
  classical
  ext v
  by_cases hb : bit C v (residualCoord n) = false
  · simp [mem_residualActiveSlice, hb]
  · have ht : bit C v (residualCoord n) = true := by
      cases h : bit C v (residualCoord n) <;> simp_all
    simp [mem_residualActiveSlice, hb, ht]

/-- Each slice's completion mass is at most twice the profile surplus carried
by vertices in that slice. -/
theorem residualSlice_mass_le_two_surplus
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (b : Bool)
    (hstrict :
      ∀ v, residualCoord n ∈ active C v →
        exponent v + 1 ≤ projectedFree C v) :
    (residualSliceCompletionWords C b).card ≤
      2 * ∑ v ∈ residualActiveSlice C b,
        dyadicProfileSurplus exponent (projectedFree C) v := by
  rw [residualSliceCompletionWords_card C b]
  calc
    (∑ v ∈ residualActiveSlice C b,
      (retainedCompletionWords C v).card)
        =
      ∑ v ∈ residualActiveSlice C b,
        2 ^ projectedFree C v := by
          apply Finset.sum_congr rfl
          intro v hv
          rw [retainedCompletionWords_card]
          rfl
    _ ≤
      ∑ v ∈ residualActiveSlice C b,
        2 * dyadicProfileSurplus exponent (projectedFree C) v := by
          apply Finset.sum_le_sum
          intro v hv
          have hvData :=
            (mem_residualActiveSlice C b v).1 hv
          exact projectedCube_le_two_mul_surplus_of_strict
            C exponent v (hstrict v hvData.1)
    _ =
      2 * ∑ v ∈ residualActiveSlice C b,
        dyadicProfileSurplus exponent (projectedFree C) v := by
          rw [Finset.mul_sum]

/-- Main global payment theorem. -/
theorem overlap_le_totalSurplus_of_residualActive_strict
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hstrict :
      ∀ v, residualCoord n ∈ active C v →
        exponent v + 1 ≤ projectedFree C v) :
    (overlapCompletionWords C).card ≤
      totalDyadicProfileSurplus exponent (projectedFree C) := by
  classical
  let S0 := residualActiveSlice C false
  let S1 := residualActiveSlice C true
  let A0 := residualSliceCompletionWords C false
  let A1 := residualSliceCompletionWords C true
  have hO0 :
      (overlapCompletionWords C).card ≤ A0.card := by
    rw [overlapCompletionWords_eq_slice_inter C]
    exact Finset.card_le_card Finset.inter_subset_left
  have hO1 :
      (overlapCompletionWords C).card ≤ A1.card := by
    rw [overlapCompletionWords_eq_slice_inter C]
    exact Finset.card_le_card Finset.inter_subset_right
  have hhalf :
      2 * (overlapCompletionWords C).card ≤
        A0.card + A1.card := by
    omega
  have hA0 :
      A0.card ≤
        2 * ∑ v ∈ S0,
          dyadicProfileSurplus exponent (projectedFree C) v := by
    simpa [A0, S0] using
      residualSlice_mass_le_two_surplus
        C exponent false hstrict
  have hA1 :
      A1.card ≤
        2 * ∑ v ∈ S1,
          dyadicProfileSurplus exponent (projectedFree C) v := by
    simpa [A1, S1] using
      residualSlice_mass_le_two_surplus
        C exponent true hstrict
  have hslice :
      (overlapCompletionWords C).card ≤
        (∑ v ∈ S0,
          dyadicProfileSurplus exponent (projectedFree C) v) +
        (∑ v ∈ S1,
          dyadicProfileSurplus exponent (projectedFree C) v) := by
    omega
  have hdisj : Disjoint S0 S1 := by
    simpa [S0, S1] using residualActiveSlice_disjoint C
  have hunion :
      (∑ v ∈ S0,
          dyadicProfileSurplus exponent (projectedFree C) v) +
        (∑ v ∈ S1,
          dyadicProfileSurplus exponent (projectedFree C) v)
        =
      ∑ v ∈ S0 ∪ S1,
        dyadicProfileSurplus exponent (projectedFree C) v := by
    symm
    exact Finset.sum_union hdisj
  rw [hunion] at hslice
  unfold totalDyadicProfileSurplus
  exact hslice.trans
    (Finset.sum_le_sum_of_subset
      (by
        intro v hv
        simp))

/-- If there is no projected-saturated residual-active vertex, the overlap
part of the residual master inequality is already closed. -/
theorem overlap_le_totalSurplus_of_no_saturated_residualActive
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hbudget :
      ∀ v, residualCoord n ∈ active C v →
        exponent v ≤ projectedFree C v)
    (hnotSat :
      ∀ v, residualCoord n ∈ active C v →
        exponent v ≠ projectedFree C v) :
    (overlapCompletionWords C).card ≤
      totalDyadicProfileSurplus exponent (projectedFree C) := by
  apply overlap_le_totalSurplus_of_residualActive_strict
  intro v hres
  have hle := hbudget v hres
  have hne := hnotSat v hres
  omega

#print axioms projectedCube_le_two_mul_surplus_of_strict
#print axioms residualSlice_mass_le_two_surplus
#print axioms overlap_le_totalSurplus_of_residualActive_strict
#print axioms overlap_le_totalSurplus_of_no_saturated_residualActive

end OrderedEdgeColoring
end JSP000404Research
