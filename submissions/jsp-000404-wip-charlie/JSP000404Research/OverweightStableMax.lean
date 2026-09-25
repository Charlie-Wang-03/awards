import JSP000404Research.DeletionAveraging
import Mathlib.Tactic

/-!
# Maximal exponent centres are stable when no deletion is compensated

Let weight(i)=2^exponent(i).  Suppose bonus(i,r) is a nonnegative contribution
made by survivor i when r is deleted, and for every deletion r

  old survivor mass + total bonus in column r <= post(r).

If no deletion is compensated, post(r) is strictly below the old total mass.
Consequently the whole bonus column is strictly smaller than the deleted
weight weight(r).

Call i bonus-stable if no single deletion column receives a contribution from i
as large as weight(i).

If a maximal-exponent centre i were not stable, some deletion r would receive
bonus(i,r) >= weight(i).  The column bound would then give

  weight(i) <= bonus(i,r) <= totalBonus(r) < weight(r),

hence exponent(i)<exponent(r), contradicting maximality.

This is the abstract minimal-counterexample bridge from deletion bonuses to
the local stable-centre geometry.
-/

namespace JSP000404Research

open scoped BigOperators

def BonusStable
    {V : Type*}
    (exponent : V → ℕ)
    (bonus : V → V → ℕ)
    (i : V) : Prop :=
  ∀ r, bonus i r < 2 ^ exponent i

/-- If a deletion is not compensated, its total bonus is smaller than the
weight of the deleted centre. -/
theorem total_bonus_lt_deleted_weight_of_no_compensated
    {V : Type*} [Fintype V]
    (exponent post : V → ℕ)
    (bonus : V → V → ℕ)
    (r : V)
    (hpoint :
      (∑ i ∈ Finset.univ.erase r, 2 ^ exponent i) +
          (∑ i : V, bonus i r) ≤ post r)
    (hnocomp :
      post r < ∑ i : V, 2 ^ exponent i) :
    (∑ i : V, bonus i r) < 2 ^ exponent r := by
  classical
  have hsplit :
      (∑ i : V, 2 ^ exponent i) =
        2 ^ exponent r +
          ∑ i ∈ Finset.univ.erase r, 2 ^ exponent i := by
    rw [← Finset.add_sum_erase
      (Finset.univ : Finset V)
      (fun i => 2 ^ exponent i)
      (Finset.mem_univ r)]
    omega
  rw [hsplit] at hnocomp
  omega

/-- Pointwise form under a global no-compensated-deletion hypothesis. -/
theorem every_bonus_column_lt_deleted_weight
    {V : Type*} [Fintype V]
    (exponent post : V → ℕ)
    (bonus : V → V → ℕ)
    (hpoint : ∀ r,
      (∑ i ∈ Finset.univ.erase r, 2 ^ exponent i) +
          (∑ i : V, bonus i r) ≤ post r)
    (hnocomp : ∀ r,
      post r < ∑ i : V, 2 ^ exponent i) :
    ∀ r,
      (∑ i : V, bonus i r) < 2 ^ exponent r := by
  intro r
  exact total_bonus_lt_deleted_weight_of_no_compensated
    exponent post bonus r (hpoint r) (hnocomp r)

/-- A centre with maximal exponent is bonus-stable whenever no deletion is
compensated. -/
theorem bonusStable_of_max_exponent_of_no_compensated
    {V : Type*} [Fintype V]
    (exponent post : V → ℕ)
    (bonus : V → V → ℕ)
    (hpoint : ∀ r,
      (∑ i ∈ Finset.univ.erase r, 2 ^ exponent i) +
          (∑ i : V, bonus i r) ≤ post r)
    (hnocomp : ∀ r,
      post r < ∑ i : V, 2 ^ exponent i)
    (i : V)
    (hmax : ∀ j, exponent j ≤ exponent i) :
    BonusStable exponent bonus i := by
  intro r
  have hcol :
      (∑ j : V, bonus j r) < 2 ^ exponent r :=
    every_bonus_column_lt_deleted_weight
      exponent post bonus hpoint hnocomp r
  have hterm :
      bonus i r ≤ ∑ j : V, bonus j r := by
    exact Finset.single_le_sum
      (fun _ _ => Nat.zero_le _)
      (Finset.mem_univ i)
  by_contra hnot
  have hself :
      2 ^ exponent i ≤ bonus i r := by
    omega
  have hp :
      2 ^ exponent i < 2 ^ exponent r :=
    hself.trans_lt (hterm.trans_lt hcol)
  have hexp :
      exponent i < exponent r := by
    exact (Nat.pow_lt_pow_iff_right₀
      (by norm_num : 1 < 2)).1 hp
  exact (not_lt_of_ge (hmax r)) hexp

/-- Contrapositive: if a maximal-exponent centre has one full self-weight
bonus in some deletion, that deletion must already be compensated. -/
theorem exists_compensated_deletion_of_max_exponent_self_bonus
    {V : Type*} [Fintype V] [Nonempty V]
    (exponent post : V → ℕ)
    (bonus : V → V → ℕ)
    (hpoint : ∀ r,
      (∑ i ∈ Finset.univ.erase r, 2 ^ exponent i) +
          (∑ i : V, bonus i r) ≤ post r)
    (i : V)
    (hmax : ∀ j, exponent j ≤ exponent i)
    (hunstable :
      ∃ r, 2 ^ exponent i ≤ bonus i r) :
    ∃ r,
      (∑ j : V, 2 ^ exponent j) ≤ post r := by
  by_contra hnone
  push_neg at hnone
  have hstable :=
    bonusStable_of_max_exponent_of_no_compensated
      exponent post bonus hpoint hnone i hmax
  obtain ⟨r, hr⟩ := hunstable
  exact (not_lt_of_ge hr) (hstable r)

#print axioms total_bonus_lt_deleted_weight_of_no_compensated
#print axioms bonusStable_of_max_exponent_of_no_compensated
#print axioms exists_compensated_deletion_of_max_exponent_self_bonus

end JSP000404Research
