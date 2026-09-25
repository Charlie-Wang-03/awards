
import JSP000404Research.UnitGainDeletionBonus
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic

/-!
# Dyadic rigidity of a minimal overweight deletion step

Let the old weights be powers of two

  weight(i) = 2 ^ exponent(i),

and let after(r,i) be the survivor exponent after deleting r.

Assume:

* exponent(i) <= n for every i;
* survivor exponents never decrease;
* the old total weight W is strictly larger than 2^n;
* every deletion child has post weight at most 2^n.

Fix a vertex r of minimum old exponent a.

The old survivor mass after merely removing r is at most the actual post mass,
hence at most 2^n.  Therefore

  0 < E := W - 2^n <= 2^a.

But every old dyadic weight and 2^n is divisible by 2^a.  Hence E is a
positive multiple of 2^a.  The previous inequality forces

  E = 2^a.

Consequently deleting ANY minimum-exponent vertex removes exactly the whole
overweight excess:

  sum_{i != r} 2^exponent(i) = 2^n.

Monotonicity and the child upper bound then force equality throughout:

  postWeight(r) = 2^n,

and every surviving exponent is unchanged pointwise.

This is substantially stronger than merely extracting one maximal stable
centre from an uncompensated configuration.
-/

namespace JSP000404Research

open scoped BigOperators

/-- Old dyadic survivor mass with r removed. -/
def oldDeletionWeight
    {V : Type*} [Fintype V]
    (exponent : V → ℕ)
    (r : V) : ℕ :=
  ∑ i ∈ Finset.univ.erase r, 2 ^ exponent i

/-- Split the full old weight into the deleted term and the old survivor
mass. -/
theorem totalDyadicWeight_eq_deleted_add_oldDeletionWeight
    {V : Type*} [Fintype V]
    (exponent : V → ℕ)
    (r : V) :
    (∑ i : V, 2 ^ exponent i) =
      2 ^ exponent r + oldDeletionWeight exponent r := by
  classical
  unfold oldDeletionWeight
  rw [← Finset.add_sum_erase
    (Finset.univ : Finset V)
    (fun i => 2 ^ exponent i)
    (Finset.mem_univ r)]

/-- Survivor monotonicity compares the old survivor mass with the actual
post-deletion mass. -/
theorem oldDeletionWeight_le_post_of_exponent_mono
    {V : Type*} [Fintype V]
    (exponent : V → ℕ)
    (after : V → V → ℕ)
    (hmono :
      ∀ r i, i ≠ r → exponent i ≤ after r i)
    (r : V) :
    oldDeletionWeight exponent r ≤
      deletionPostWeight after r := by
  classical
  unfold oldDeletionWeight deletionPostWeight
  apply Finset.sum_le_sum
  intro i hi
  have hir : i ≠ r :=
    (Finset.mem_erase.mp hi).1
  exact Nat.pow_le_pow_right
    (by norm_num : 0 < 2)
    (hmono r i hir)

/-- A minimum dyadic atom divides the full old weight. -/
theorem minDyadicWeight_dvd_total
    {V : Type*} [Fintype V]
    (exponent : V → ℕ)
    (r : V)
    (hmin : ∀ i : V, exponent r ≤ exponent i) :
    2 ^ exponent r ∣ ∑ i : V, 2 ^ exponent i := by
  classical
  apply Finset.dvd_sum
  intro i hi
  exact pow_dvd_pow 2 (hmin i)


/-- One-column form of the arithmetic rigidity.

Only the chosen minimum vertex r needs a bounded deletion child.  This is the
form compatible with exact-normalization induction, where one may only know
that deleting r preserves the maximizing angle parameter. -/
theorem minimal_overweight_excess_eq_min_weight_of_child_bound
    {V : Type*} [Fintype V]
    (exponent : V → ℕ)
    (after : V → V → ℕ)
    (n : ℕ)
    (r : V)
    (hexp : ∀ i : V, exponent i ≤ n)
    (hmonoR :
      ∀ i, i ≠ r → exponent i ≤ after r i)
    (hover :
      2 ^ n < ∑ i : V, 2 ^ exponent i)
    (hchildR :
      deletionPostWeight after r ≤ 2 ^ n)
    (hmin : ∀ i : V, exponent r ≤ exponent i) :
    (∑ i : V, 2 ^ exponent i) - 2 ^ n =
      2 ^ exponent r := by
  classical
  let W : ℕ := ∑ i : V, 2 ^ exponent i
  let B : ℕ := 2 ^ n
  let d : ℕ := 2 ^ exponent r
  have hsurv :
      oldDeletionWeight exponent r ≤ B := by
    have hmonoSum :
        oldDeletionWeight exponent r ≤
          deletionPostWeight after r := by
      unfold oldDeletionWeight deletionPostWeight
      apply Finset.sum_le_sum
      intro i hi
      have hir : i ≠ r :=
        (Finset.mem_erase.mp hi).1
      exact Nat.pow_le_pow_right
        (by norm_num : 0 < 2)
        (hmonoR i hir)
    exact hmonoSum.trans hchildR
  have hsplit :
      W = d + oldDeletionWeight exponent r := by
    simpa [W, d] using
      totalDyadicWeight_eq_deleted_add_oldDeletionWeight
        exponent r
  have hBW : B < W := by
    simpa [B, W] using hover
  have hEpos : 0 < W - B := by omega
  have hEle : W - B ≤ d := by omega
  have hdvdW : d ∣ W := by
    simpa [d, W] using
      minDyadicWeight_dvd_total exponent r hmin
  have hdvdB : d ∣ B := by
    dsimp [d, B]
    exact pow_dvd_pow 2 (hexp r)
  have hdvdE : d ∣ W - B :=
    Nat.dvd_sub hdvdW hdvdB
  have hdleE : d ≤ W - B :=
    Nat.le_of_dvd hEpos hdvdE
  have hEq : W - B = d :=
    le_antisymm hEle hdleE
  simpa [W, B, d] using hEq

/-- One-column form: old survivor mass after deleting the chosen minimum vertex
is exactly the sharp bound. -/
theorem oldDeletionWeight_eq_bound_of_minimum_child_bound
    {V : Type*} [Fintype V]
    (exponent : V → ℕ)
    (after : V → V → ℕ)
    (n : ℕ)
    (r : V)
    (hexp : ∀ i : V, exponent i ≤ n)
    (hmonoR :
      ∀ i, i ≠ r → exponent i ≤ after r i)
    (hover :
      2 ^ n < ∑ i : V, 2 ^ exponent i)
    (hchildR :
      deletionPostWeight after r ≤ 2 ^ n)
    (hmin : ∀ i : V, exponent r ≤ exponent i) :
    oldDeletionWeight exponent r = 2 ^ n := by
  have hsplit :=
    totalDyadicWeight_eq_deleted_add_oldDeletionWeight
      exponent r
  have hexcess :=
    minimal_overweight_excess_eq_min_weight_of_child_bound
      exponent after n r hexp hmonoR hover hchildR hmin
  have hle :
      2 ^ n ≤ ∑ i : V, 2 ^ exponent i :=
    le_of_lt hover
  omega

/-- One-column form: the chosen deletion post mass itself is exactly 2^n. -/
theorem deletionPostWeight_eq_bound_of_minimum_child_bound
    {V : Type*} [Fintype V]
    (exponent : V → ℕ)
    (after : V → V → ℕ)
    (n : ℕ)
    (r : V)
    (hexp : ∀ i : V, exponent i ≤ n)
    (hmonoR :
      ∀ i, i ≠ r → exponent i ≤ after r i)
    (hover :
      2 ^ n < ∑ i : V, 2 ^ exponent i)
    (hchildR :
      deletionPostWeight after r ≤ 2 ^ n)
    (hmin : ∀ i : V, exponent r ≤ exponent i) :
    deletionPostWeight after r = 2 ^ n := by
  have hold :=
    oldDeletionWeight_eq_bound_of_minimum_child_bound
      exponent after n r hexp hmonoR hover hchildR hmin
  have hmonoSum :
      oldDeletionWeight exponent r ≤
        deletionPostWeight after r := by
    classical
    unfold oldDeletionWeight deletionPostWeight
    apply Finset.sum_le_sum
    intro i hi
    have hir : i ≠ r :=
      (Finset.mem_erase.mp hi).1
    exact Nat.pow_le_pow_right
      (by norm_num : 0 < 2)
      (hmonoR i hir)
  omega

/-- One-column pointwise rigidity: every survivor exponent stays unchanged. -/
theorem survivor_exponent_eq_of_minimum_child_bound
    {V : Type*} [Fintype V]
    (exponent : V → ℕ)
    (after : V → V → ℕ)
    (n : ℕ)
    (hexp : ∀ i : V, exponent i ≤ n)
    (hmonoR :
      ∀ i, i ≠ r → exponent i ≤ after r i)
    (hover :
      2 ^ n < ∑ i : V, 2 ^ exponent i)
    (hchildR :
      deletionPostWeight after r ≤ 2 ^ n)
    (r i : V)
    (hmin : ∀ j : V, exponent r ≤ exponent j)
    (hir : i ≠ r) :
    after r i = exponent i := by
  classical
  let S : Finset V := Finset.univ.erase r
  let f : V → ℕ := fun j => 2 ^ exponent j
  let g : V → ℕ := fun j => 2 ^ after r j
  have hiS : i ∈ S := by
    simp [S, hir]
  have hfg :
      ∀ j ∈ S, f j ≤ g j := by
    intro j hj
    have hjr : j ≠ r :=
      (Finset.mem_erase.mp hj).1
    exact Nat.pow_le_pow_right
      (by norm_num : 0 < 2)
      (hmonoR j hjr)
  have hsumEq :
      (∑ j ∈ S, f j) = ∑ j ∈ S, g j := by
    have hold :=
      oldDeletionWeight_eq_bound_of_minimum_child_bound
        exponent after n r hexp hmonoR hover hchildR hmin
    have hpost :=
      deletionPostWeight_eq_bound_of_minimum_child_bound
        exponent after n r hexp hmonoR hover hchildR hmin
    simpa [S, f, g, oldDeletionWeight,
      deletionPostWeight] using hold.trans hpost.symm
  have hfiLe : f i ≤ g i := hfg i hiS
  have hfiEq : f i = g i := by
    by_contra hne
    have hfiLt : f i < g i :=
      lt_of_le_of_ne hfiLe hne
    let T := S.erase i
    have hrest :
        (∑ j ∈ T, f j) ≤ ∑ j ∈ T, g j := by
      apply Finset.sum_le_sum
      intro j hj
      exact hfg j (Finset.mem_of_mem_erase hj)
    have hsplitF :
        (∑ j ∈ S, f j) =
          f i + ∑ j ∈ T, f j := by
      dsimp [T]
      rw [← Finset.add_sum_erase S f hiS]
    have hsplitG :
        (∑ j ∈ S, g j) =
          g i + ∑ j ∈ T, g j := by
      dsimp [T]
      rw [← Finset.add_sum_erase S g hiS]
    rw [hsplitF, hsplitG] at hsumEq
    omega
  have hle := hmonoR i hir
  by_contra hneExp
  have hlt : exponent i < after r i := by omega
  have hpLt :
      2 ^ exponent i < 2 ^ after r i :=
    Nat.pow_lt_pow_right (by norm_num : 1 < 2) hlt
  exact (ne_of_lt hpLt) hfiEq

/-- Full one-column rigidity package. -/
theorem minimum_deletion_rigidity_of_child_bound
    {V : Type*} [Fintype V]
    (exponent : V → ℕ)
    (after : V → V → ℕ)
    (n : ℕ)
    (r : V)
    (hexp : ∀ i : V, exponent i ≤ n)
    (hmonoR :
      ∀ i, i ≠ r → exponent i ≤ after r i)
    (hover :
      2 ^ n < ∑ i : V, 2 ^ exponent i)
    (hchildR :
      deletionPostWeight after r ≤ 2 ^ n)
    (hmin : ∀ i : V, exponent r ≤ exponent i) :
    (∑ i : V, 2 ^ exponent i) - 2 ^ n =
        2 ^ exponent r
      ∧
    oldDeletionWeight exponent r = 2 ^ n
      ∧
    deletionPostWeight after r = 2 ^ n
      ∧
    ∀ i : V, i ≠ r → after r i = exponent i := by
  refine ⟨
    minimal_overweight_excess_eq_min_weight_of_child_bound
      exponent after n r hexp hmonoR hover hchildR hmin,
    oldDeletionWeight_eq_bound_of_minimum_child_bound
      exponent after n r hexp hmonoR hover hchildR hmin,
    deletionPostWeight_eq_bound_of_minimum_child_bound
      exponent after n r hexp hmonoR hover hchildR hmin,
    ?_⟩
  intro i hir
  exact survivor_exponent_eq_of_minimum_child_bound
    exponent after n hexp hmonoR hover hchildR
    r i hmin hir

/-- Main arithmetic rigidity: the overweight excess is exactly one minimum
old dyadic weight. -/
theorem minimal_overweight_excess_eq_min_weight
    {V : Type*} [Fintype V]
    (exponent : V → ℕ)
    (after : V → V → ℕ)
    (n : ℕ)
    (hexp : ∀ i : V, exponent i ≤ n)
    (hmono :
      ∀ r i, i ≠ r → exponent i ≤ after r i)
    (hover :
      2 ^ n < ∑ i : V, 2 ^ exponent i)
    (hchild :
      ∀ r : V, deletionPostWeight after r ≤ 2 ^ n)
    (r : V)
    (hmin : ∀ i : V, exponent r ≤ exponent i) :
    (∑ i : V, 2 ^ exponent i) - 2 ^ n =
      2 ^ exponent r := by
  classical
  let W : ℕ := ∑ i : V, 2 ^ exponent i
  let B : ℕ := 2 ^ n
  let d : ℕ := 2 ^ exponent r
  have hsurv :
      oldDeletionWeight exponent r ≤ B := by
    exact (oldDeletionWeight_le_post_of_exponent_mono
      exponent after hmono r).trans (hchild r)
  have hsplit :
      W = d + oldDeletionWeight exponent r := by
    simpa [W, d] using
      totalDyadicWeight_eq_deleted_add_oldDeletionWeight
        exponent r
  have hBW : B < W := by
    simpa [B, W] using hover
  have hEpos : 0 < W - B := by
    omega
  have hEle : W - B ≤ d := by
    omega
  have hdvdW : d ∣ W := by
    simpa [d, W] using
      minDyadicWeight_dvd_total exponent r hmin
  have hdvdB : d ∣ B := by
    dsimp [d, B]
    exact pow_dvd_pow 2 (hexp r)
  have hdvdE : d ∣ W - B :=
    Nat.dvd_sub hdvdW hdvdB
  have hdPos : 0 < d := by
    dsimp [d]
    positivity
  have hdleE : d ≤ W - B :=
    Nat.le_of_dvd hEpos hdvdE
  have hEq : W - B = d :=
    le_antisymm hEle hdleE
  simpa [W, B, d] using hEq

/-- Removing any minimum-exponent vertex leaves old survivor mass exactly at
the sharp dyadic bound. -/
theorem oldDeletionWeight_eq_bound_of_minimal_overweight
    {V : Type*} [Fintype V]
    (exponent : V → ℕ)
    (after : V → V → ℕ)
    (n : ℕ)
    (hexp : ∀ i : V, exponent i ≤ n)
    (hmono :
      ∀ r i, i ≠ r → exponent i ≤ after r i)
    (hover :
      2 ^ n < ∑ i : V, 2 ^ exponent i)
    (hchild :
      ∀ r : V, deletionPostWeight after r ≤ 2 ^ n)
    (r : V)
    (hmin : ∀ i : V, exponent r ≤ exponent i) :
    oldDeletionWeight exponent r = 2 ^ n := by
  have hsplit :=
    totalDyadicWeight_eq_deleted_add_oldDeletionWeight
      exponent r
  have hexcess :=
    minimal_overweight_excess_eq_min_weight
      exponent after n hexp hmono hover hchild r hmin
  have hle :
      2 ^ n ≤ ∑ i : V, 2 ^ exponent i :=
    le_of_lt hover
  omega

/-- The actual post-deletion mass of a minimum-exponent vertex is also exactly
the sharp bound. -/
theorem deletionPostWeight_eq_bound_of_minimal_overweight
    {V : Type*} [Fintype V]
    (exponent : V → ℕ)
    (after : V → V → ℕ)
    (n : ℕ)
    (hexp : ∀ i : V, exponent i ≤ n)
    (hmono :
      ∀ r i, i ≠ r → exponent i ≤ after r i)
    (hover :
      2 ^ n < ∑ i : V, 2 ^ exponent i)
    (hchild :
      ∀ r : V, deletionPostWeight after r ≤ 2 ^ n)
    (r : V)
    (hmin : ∀ i : V, exponent r ≤ exponent i) :
    deletionPostWeight after r = 2 ^ n := by
  have hold :=
    oldDeletionWeight_eq_bound_of_minimal_overweight
      exponent after n hexp hmono hover hchild r hmin
  have hmonoSum :=
    oldDeletionWeight_le_post_of_exponent_mono
      exponent after hmono r
  have hupper := hchild r
  omega

/-- Equality of total survivor mass together with pointwise monotonicity forces
every surviving dyadic term to stay equal. -/
theorem survivor_weight_eq_of_minimum_deletion
    {V : Type*} [Fintype V]
    (exponent : V → ℕ)
    (after : V → V → ℕ)
    (n : ℕ)
    (hexp : ∀ i : V, exponent i ≤ n)
    (hmono :
      ∀ r i, i ≠ r → exponent i ≤ after r i)
    (hover :
      2 ^ n < ∑ i : V, 2 ^ exponent i)
    (hchild :
      ∀ r : V, deletionPostWeight after r ≤ 2 ^ n)
    (r i : V)
    (hmin : ∀ j : V, exponent r ≤ exponent j)
    (hir : i ≠ r) :
    2 ^ exponent i = 2 ^ after r i := by
  classical
  let S : Finset V := Finset.univ.erase r
  let f : V → ℕ := fun j => 2 ^ exponent j
  let g : V → ℕ := fun j => 2 ^ after r j
  have hiS : i ∈ S := by
    simp [S, hir]
  have hfg :
      ∀ j ∈ S, f j ≤ g j := by
    intro j hj
    have hjr : j ≠ r := by
      simpa [S] using (Finset.mem_erase.mp hj).1
    exact Nat.pow_le_pow_right
      (by norm_num : 0 < 2)
      (hmono r j hjr)
  have hsumEq :
      (∑ j ∈ S, f j) = ∑ j ∈ S, g j := by
    have hold :=
      oldDeletionWeight_eq_bound_of_minimal_overweight
        exponent after n hexp hmono hover hchild r hmin
    have hpost :=
      deletionPostWeight_eq_bound_of_minimal_overweight
        exponent after n hexp hmono hover hchild r hmin
    simpa [S, f, g, oldDeletionWeight,
      deletionPostWeight] using hold.trans hpost.symm
  have hfiLe : f i ≤ g i :=
    hfg i hiS
  by_contra hne
  have hfiLt : f i < g i := lt_of_le_of_ne hfiLe hne
  let T := S.erase i
  have hrest :
      (∑ j ∈ T, f j) ≤ ∑ j ∈ T, g j := by
    apply Finset.sum_le_sum
    intro j hj
    apply hfg j
    exact Finset.mem_of_mem_erase hj
  have hsplitF :
      (∑ j ∈ S, f j) =
        f i + ∑ j ∈ T, f j := by
    dsimp [T]
    rw [← Finset.add_sum_erase S f hiS]
  have hsplitG :
      (∑ j ∈ S, g j) =
        g i + ∑ j ∈ T, g j := by
    dsimp [T]
    rw [← Finset.add_sum_erase S g hiS]
  rw [hsplitF, hsplitG] at hsumEq
  omega

/-- Strongest form: deleting a minimum-exponent vertex leaves every survivor
exponent unchanged pointwise. -/
theorem survivor_exponent_eq_of_minimum_deletion
    {V : Type*} [Fintype V]
    (exponent : V → ℕ)
    (after : V → V → ℕ)
    (n : ℕ)
    (hexp : ∀ i : V, exponent i ≤ n)
    (hmono :
      ∀ r i, i ≠ r → exponent i ≤ after r i)
    (hover :
      2 ^ n < ∑ i : V, 2 ^ exponent i)
    (hchild :
      ∀ r : V, deletionPostWeight after r ≤ 2 ^ n)
    (r i : V)
    (hmin : ∀ j : V, exponent r ≤ exponent j)
    (hir : i ≠ r) :
    after r i = exponent i := by
  have hle := hmono r i hir
  have hpow :=
    survivor_weight_eq_of_minimum_deletion
      exponent after n hexp hmono hover hchild
      r i hmin hir
  by_contra hne
  have hlt : exponent i < after r i := by
    omega
  have hpLt :
      2 ^ exponent i < 2 ^ after r i :=
    Nat.pow_lt_pow_right (by norm_num : 1 < 2) hlt
  exact (ne_of_lt hpLt) hpow

/-- Full rigidity package for one minimum-exponent deleted vertex. -/
theorem minimum_deletion_rigidity
    {V : Type*} [Fintype V]
    (exponent : V → ℕ)
    (after : V → V → ℕ)
    (n : ℕ)
    (hexp : ∀ i : V, exponent i ≤ n)
    (hmono :
      ∀ r i, i ≠ r → exponent i ≤ after r i)
    (hover :
      2 ^ n < ∑ i : V, 2 ^ exponent i)
    (hchild :
      ∀ r : V, deletionPostWeight after r ≤ 2 ^ n)
    (r : V)
    (hmin : ∀ i : V, exponent r ≤ exponent i) :
    (∑ i : V, 2 ^ exponent i) - 2 ^ n =
        2 ^ exponent r
      ∧
    oldDeletionWeight exponent r = 2 ^ n
      ∧
    deletionPostWeight after r = 2 ^ n
      ∧
    ∀ i : V, i ≠ r → after r i = exponent i := by
  refine ⟨
    minimal_overweight_excess_eq_min_weight
      exponent after n hexp hmono hover hchild r hmin,
    oldDeletionWeight_eq_bound_of_minimal_overweight
      exponent after n hexp hmono hover hchild r hmin,
    deletionPostWeight_eq_bound_of_minimal_overweight
      exponent after n hexp hmono hover hchild r hmin,
    ?_⟩
  intro i hir
  exact survivor_exponent_eq_of_minimum_deletion
    exponent after n hexp hmono hover hchild r i hmin hir

#print axioms minimal_overweight_excess_eq_min_weight
#print axioms oldDeletionWeight_eq_bound_of_minimal_overweight
#print axioms deletionPostWeight_eq_bound_of_minimal_overweight
#print axioms survivor_exponent_eq_of_minimum_deletion
#print axioms minimum_deletion_rigidity

end JSP000404Research
