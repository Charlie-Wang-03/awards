import JSP000404Research.PlanarLowerTwoFourNoTopCapacity
import Mathlib.Tactic

/-!
# Saturation forces every actual exponent to vanish at n=2, four centres

There is a sharp *if and only if* gap in the four-centre n=2 branch:
since four dyadic terms are all >=1, their sum can be <=4 only when all
four exponents vanish. The previously kernel-closed no-top case gives
the reverse implication because actual centre exponents are <2.

Thus the entire remaining geometric four-centre n=2 obligation is EXACTLY
the exclusion of a unit-deficit (exponent 1 / sharp) actual centre.
This file does NOT establish that geometric exclusion from AngleCap.
-/

namespace JSP000404Research

theorem saturated_dyadic_capacity_iff_all_zero
    {V : Type*} [Fintype V]
    (e : V → ℕ) (n : ℕ)
    (hcard : Fintype.card V = (2 : ℕ) ^ n) :
    (∑ i : V, (2 : ℕ) ^ e i) ≤ 2 ^ n ↔
      ∀ i : V, e i = 0 := by
  classical
  constructor
  · intro hsum i
    by_contra hnonzero
    have hbase : ∀ j : V, (1 : ℕ) ≤ (2 : ℕ) ^ e j := by
      intro j
      have hp : 0 < (2 : ℕ) ^ e j := pow_pos (by norm_num) _
      omega
    have hstrict : (1 : ℕ) < (2 : ℕ) ^ e i := by
      cases he : e i with
      | zero => exact False.elim (hnonzero he)
      | succ k =>
          rw [pow_succ]
          have hp : 0 < (2 : ℕ) ^ k := pow_pos (by norm_num) _
          omega
    have hstrictSum :
        (∑ j : V, (1 : ℕ)) <
          (∑ j : V, (2 : ℕ) ^ e j) := by
      apply Finset.sum_lt_sum
      · intro j _
        exact hbase j
      · exact ⟨i, Finset.mem_univ i, hstrict⟩
    have hbaseSum : (∑ _ : V, (1 : ℕ)) = 2 ^ n := by
      simpa using hcard
    omega
  · intro hzero
    calc
      (∑ i : V, (2 : ℕ) ^ e i) =
          (∑ _ : V, (1 : ℕ)) := by
        apply Finset.sum_congr rfl
        intro i _
        simp [hzero i]
      _ = Fintype.card V := by simp
      _ ≤ (2 : ℕ) ^ n := le_of_eq hcard

namespace ProjectionOrdered

theorem planar_lower_branch_n_two_four_capacity_iff_no_top
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
        CentreProjectiveCycle (reindexedPoint_injective hp) i) :
    letI : LinearOrder (ProjectionOrdered V) := projectionLinearOrder hp
    ((∑ i : ProjectionOrdered V,
      (2 : ℕ) ^ centreExponent (cycles i) t) ≤ 2 ^ 2 ↔
       ∀ i : ProjectionOrdered V,
         centreExponent (cycles i) t ≠ 1) := by
  letI : LinearOrder (ProjectionOrdered V) := projectionLinearOrder hp
  constructor
  · intro hsum i
    have hz :=
      (saturated_dyadic_capacity_iff_all_zero
        (fun i : ProjectionOrdered V => centreExponent (cycles i) t)
        2 (by simpa using hcard)).mp hsum i
    omega
  · intro hnoTop
    exact planar_lower_branch_n_two_four_no_top_capacity
      hp hcap hcard hdelta0 hdeltaHalf ht hlam cycles hnoTop

#print axioms saturated_dyadic_capacity_iff_all_zero
#print axioms planar_lower_branch_n_two_four_capacity_iff_no_top

end ProjectionOrdered
end JSP000404Research
