import JSP000404Research.ResidualUnsafeZeroZeroRigidity
import JSP000404Research.ConcreteMinimumOverweightRigidity
import Mathlib.Tactic

/-!
# Minimal-overweight deletion rigidity at a zero-exponent centre

A zero--zero unsafe saturated carrier has endpoint exponent zero.  Since all
centre exponents are natural numbers, either endpoint is automatically a
minimum-exponent centre.

Therefore in a minimal overweight induction step, once the deletion child is
bounded by 2^n, deleting such an endpoint is completely rigid:

* the overweight excess is exactly one;
* the deletion child has post weight exactly 2^n;
* every surviving centre keeps its exponent;
* at every survivor, the ray to the deleted zero endpoint has a zero quotient
  on at least one cyclic side.

This is the exact interface between the terminal zero--zero residual defect
and the existing compensated-deletion induction.
-/

namespace JSP000404Research

open scoped BigOperators

/-- Exponent zero is automatically globally minimal. -/
theorem zero_exponent_is_minimum
    {V : Type*}
    (exponent : V → ℕ)
    {r : V}
    (hr : exponent r = 0) :
    ∀ i : V, exponent r ≤ exponent i := by
  intro i
  rw [hr]
  exact Nat.zero_le _

/-- One-child arithmetic rigidity specialized to a zero minimum: the total
overweight excess is exactly one. -/
theorem zero_minimum_overweight_excess_eq_one_of_child_bound
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
    (hrZero : exponent r = 0) :
    (∑ i : V, 2 ^ exponent i) = 2 ^ n + 1 := by
  have hmin : ∀ i : V, exponent r ≤ exponent i :=
    zero_exponent_is_minimum exponent hrZero
  have hexcess :=
    minimal_overweight_excess_eq_min_weight_of_child_bound
      exponent after n r hexp hmonoR hover hchildR hmin
  rw [hrZero] at hexcess
  norm_num at hexcess
  have hle : 2 ^ n ≤ ∑ i : V, 2 ^ exponent i :=
    le_of_lt hover
  omega

/-- Concrete planar specialization: deleting any zero-exponent centre in a
minimal overweight step leaves every survivor exponent unchanged. -/
theorem zero_centre_deletion_survivor_exponent_eq_of_child_bound
    {V : Type*} [LinearOrder V] [Fintype V] [Nonempty V]
    {p : V → Plane} {hp : Function.Injective p}
    (C : ∀ i : V, CentreProjectiveCycle hp i)
    (hcard : 3 ≤ Fintype.card V)
    {t : ℝ}
    (ht : 0 ≤ t)
    (n : ℕ)
    (r i : V)
    (hexp :
      ∀ j : V, centreExponent (C j) t ≤ n)
    (hover :
      2 ^ n < ∑ j : V, 2 ^ centreExponent (C j) t)
    (hchildR :
      deletionPostWeight
        (concreteDeletionAfter C hcard t) r ≤ 2 ^ n)
    (hrZero :
      centreExponent (C r) t = 0)
    (hir : i ≠ r) :
    centreExponent
        ((C i).restrictDelete r hir
          (child_other_nonempty_of_card_ge_three hcard hir)) t
      =
    centreExponent (C i) t := by
  apply
    concrete_minimum_deletion_survivor_exponent_eq_of_child_bound
      C hcard ht n r i hexp hover hchildR
  · exact zero_exponent_is_minimum
      (fun j => centreExponent (C j) t) hrZero
  · exact hir

/-- Geometric specialization: at every survivor, the ray to a deleted
zero-exponent centre has a zero quotient on at least one adjacent cyclic side. -/
theorem zero_deleted_ray_adjacent_zero_at_survivor_of_child_bound
    {V : Type*} [LinearOrder V] [Fintype V] [Nonempty V]
    {p : V → Plane} {hp : Function.Injective p}
    (C : ∀ i : V, CentreProjectiveCycle hp i)
    (hcard : 3 ≤ Fintype.card V)
    {t : ℝ}
    (ht : 0 ≤ t)
    (n : ℕ)
    (r i : V)
    (hexp :
      ∀ j : V, centreExponent (C j) t ≤ n)
    (hover :
      2 ^ n < ∑ j : V, 2 ^ centreExponent (C j) t)
    (hchildR :
      deletionPostWeight
        (concreteDeletionAfter C hcard t) r ≤ 2 ^ n)
    (hrZero :
      centreExponent (C r) t = 0)
    (hir : i ≠ r) :
    ∃ pre post : List (OtherVertex i),
      (C i).rays =
        pre ++ deletedParentRay r i hir :: post
      ∧
      match pre, post with
      | [], [] => True
      | [], b :: bs =>
          Nat.floor
            (t * ((rayThetaAt hp i b -
              rayThetaAt hp i (deletedParentRay r i hir)) /
                Real.pi)) = 0
          ∨
          Nat.floor
            (t * ((rayThetaAt hp i (deletedParentRay r i hir) +
              Real.pi -
              (bs.map (rayThetaAt hp i)).getLastD
                (rayThetaAt hp i b)) / Real.pi)) = 0
      | first :: mid, [] =>
          Nat.floor
            (t * ((rayThetaAt hp i (deletedParentRay r i hir) -
              (mid.map (rayThetaAt hp i)).getLastD
                (rayThetaAt hp i first)) / Real.pi)) = 0
          ∨
          Nat.floor
            (t * ((rayThetaAt hp i first + Real.pi -
              rayThetaAt hp i (deletedParentRay r i hir)) /
                Real.pi)) = 0
      | first :: mid, next :: tail =>
          Nat.floor
            (t * ((rayThetaAt hp i (deletedParentRay r i hir) -
              (mid.map (rayThetaAt hp i)).getLastD
                (rayThetaAt hp i first)) / Real.pi)) = 0
          ∨
          Nat.floor
            (t * ((rayThetaAt hp i next -
              rayThetaAt hp i (deletedParentRay r i hir)) /
                Real.pi)) = 0 := by
  apply
    minimum_deleted_ray_adjacent_zero_at_survivor_of_child_bound
      C hcard ht n r i hexp hover hchildR
  · exact zero_exponent_is_minimum
      (fun j => centreExponent (C j) t) hrZero
  · exact hir

#print axioms zero_minimum_overweight_excess_eq_one_of_child_bound
#print axioms zero_centre_deletion_survivor_exponent_eq_of_child_bound
#print axioms zero_deleted_ray_adjacent_zero_at_survivor_of_child_bound

end JSP000404Research
