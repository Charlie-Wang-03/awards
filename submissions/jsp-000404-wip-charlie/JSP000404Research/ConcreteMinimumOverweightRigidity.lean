
import JSP000404Research.MinimalOverweightDyadicRigidity
import JSP000404Research.ConcreteMaxStableCentre
import JSP000404Research.ConcreteDeletionStableSplit
import Mathlib.Tactic

/-!
# Concrete planar specialization of minimal-overweight dyadic rigidity

MinimalOverweightDyadicRigidity is purely arithmetic.  Here it is specialized
to the actual centre projective cycles and the genuine fixed-t deletion table.

In an overweight induction step, assume every actual deletion child is already
bounded by 2^n.  Choose any minimum-exponent centre r.

Then deleting r has total post weight exactly 2^n and EVERY surviving centre
keeps exactly its old exponent.

Consequently, at every survivor i, the parent ray pointing from i to r is a
zero-gain deletion split.  ConcreteDeletionStableSplit therefore forces at
least one of the two cyclic quotient gaps adjacent to that ray to be zero.

This is a global incidence statement tied to one common deleted vertex r,
rather than stability of just one selected maximal centre.
-/

namespace JSP000404Research

open scoped BigOperators

/-- Concrete fixed-t deletion of a minimum-exponent centre leaves every
survivor exponent unchanged. -/
theorem concrete_minimum_deletion_survivor_exponent_eq
    {V : Type*} [LinearOrder V] [Fintype V] [Nonempty V]
    {p : V → Plane} {hp : Function.Injective p}
    (C : ∀ i : V, CentreProjectiveCycle hp i)
    (hcard : 3 ≤ Fintype.card V)
    {t : ℝ}
    (ht : 0 ≤ t)
    (n : ℕ)
    (hexp :
      ∀ i : V, centreExponent (C i) t ≤ n)
    (hover :
      2 ^ n < ∑ i : V, 2 ^ centreExponent (C i) t)
    (hchild :
      ∀ r : V,
        deletionPostWeight
          (concreteDeletionAfter C hcard t) r ≤ 2 ^ n)
    (r i : V)
    (hmin :
      ∀ j : V,
        centreExponent (C r) t ≤
          centreExponent (C j) t)
    (hir : i ≠ r) :
    centreExponent
        ((C i).restrictDelete r hir
          (child_other_nonempty_of_card_ge_three hcard hir)) t
      =
    centreExponent (C i) t := by
  have hmono :
      ∀ r i, i ≠ r →
        centreExponent (C i) t ≤
          concreteDeletionAfter C hcard t r i := by
    intro r' i' hi'
    exact concreteDeletionAfter_mono
      C hcard ht hi'
  have heq :
      concreteDeletionAfter C hcard t r i =
        centreExponent (C i) t :=
    survivor_exponent_eq_of_minimum_deletion
      (fun j => centreExponent (C j) t)
      (concreteDeletionAfter C hcard t)
      n hexp hmono hover hchild
      r i hmin hir
  rw [concreteDeletionAfter_eq C hcard t hir] at heq
  exact heq

/-- The whole concrete deletion column of a minimum centre is rigid and has
post mass exactly 2^n. -/
theorem concrete_minimum_deletion_column_rigidity
    {V : Type*} [LinearOrder V] [Fintype V] [Nonempty V]
    {p : V → Plane} {hp : Function.Injective p}
    (C : ∀ i : V, CentreProjectiveCycle hp i)
    (hcard : 3 ≤ Fintype.card V)
    {t : ℝ}
    (ht : 0 ≤ t)
    (n : ℕ)
    (hexp :
      ∀ i : V, centreExponent (C i) t ≤ n)
    (hover :
      2 ^ n < ∑ i : V, 2 ^ centreExponent (C i) t)
    (hchild :
      ∀ r : V,
        deletionPostWeight
          (concreteDeletionAfter C hcard t) r ≤ 2 ^ n)
    (r : V)
    (hmin :
      ∀ j : V,
        centreExponent (C r) t ≤
          centreExponent (C j) t) :
    (∑ i : V, 2 ^ centreExponent (C i) t) - 2 ^ n =
        2 ^ centreExponent (C r) t
      ∧
    deletionPostWeight
        (concreteDeletionAfter C hcard t) r = 2 ^ n
      ∧
    ∀ i : V, i ≠ r →
      concreteDeletionAfter C hcard t r i =
        centreExponent (C i) t := by
  have hmono :
      ∀ r i, i ≠ r →
        centreExponent (C i) t ≤
          concreteDeletionAfter C hcard t r i := by
    intro r' i' hi'
    exact concreteDeletionAfter_mono C hcard ht hi'
  have hrig :=
    minimum_deletion_rigidity
      (fun j => centreExponent (C j) t)
      (concreteDeletionAfter C hcard t)
      n hexp hmono hover hchild r hmin
  refine ⟨hrig.1, hrig.2.2.1, ?_⟩
  intro i hir
  exact survivor_exponent_eq_of_minimum_deletion
    (fun j => centreExponent (C j) t)
    (concreteDeletionAfter C hcard t)
    n hexp hmono hover hchild r i hmin hir

/-- At every survivor, the ray pointing to the minimum deleted centre has at
least one zero adjacent parent quotient. -/
theorem minimum_deleted_ray_adjacent_zero_at_survivor
    {V : Type*} [LinearOrder V] [Fintype V] [Nonempty V]
    {p : V → Plane} {hp : Function.Injective p}
    (C : ∀ i : V, CentreProjectiveCycle hp i)
    (hcard : 3 ≤ Fintype.card V)
    {t : ℝ}
    (ht : 0 ≤ t)
    (n : ℕ)
    (hexp :
      ∀ i : V, centreExponent (C i) t ≤ n)
    (hover :
      2 ^ n < ∑ i : V, 2 ^ centreExponent (C i) t)
    (hchild :
      ∀ r : V,
        deletionPostWeight
          (concreteDeletionAfter C hcard t) r ≤ 2 ^ n)
    (r i : V)
    (hmin :
      ∀ j : V,
        centreExponent (C r) t ≤
          centreExponent (C j) t)
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
  obtain ⟨pre, post, hsplit⟩ :=
    exists_parent_cycle_split_at_deleted (C i) r hir
  refine ⟨pre, post, hsplit, ?_⟩
  let hother :=
    child_other_nonempty_of_card_ge_three hcard hir
  have heq :
      centreExponent
          ((C i).restrictDelete r hir hother) t =
        centreExponent (C i) t := by
    exact concrete_minimum_deletion_survivor_exponent_eq
      C hcard ht n hexp hover hchild r i hmin hir
  have hno :
      ¬ centreExponent (C i) t + 1 ≤
        centreExponent
          ((C i).restrictDelete r hir hother) t := by
    rw [heq]
    omega
  exact adjacent_zero_of_no_unit_gain
    (C i) hir hother pre post hsplit ht hno

/-- Strong negative form: at every survivor, the deleted minimum-centre ray
cannot have positive quotient gaps on both cyclic sides. -/
theorem minimum_deleted_ray_not_bothAdjacentPositive
    {V : Type*} [LinearOrder V] [Fintype V] [Nonempty V]
    {p : V → Plane} {hp : Function.Injective p}
    (C : ∀ i : V, CentreProjectiveCycle hp i)
    (hcard : 3 ≤ Fintype.card V)
    {t : ℝ}
    (ht : 0 ≤ t)
    (n : ℕ)
    (hexp :
      ∀ i : V, centreExponent (C i) t ≤ n)
    (hover :
      2 ^ n < ∑ i : V, 2 ^ centreExponent (C i) t)
    (hchild :
      ∀ r : V,
        deletionPostWeight
          (concreteDeletionAfter C hcard t) r ≤ 2 ^ n)
    (r i : V)
    (hmin :
      ∀ j : V,
        centreExponent (C r) t ≤
          centreExponent (C j) t)
    (hir : i ≠ r)
    (pre post : List (OtherVertex i))
    (hsplit :
      (C i).rays =
        pre ++ deletedParentRay r i hir :: post) :
    ¬ ParentSplitBothAdjacentPositive
      (C i) hir pre post t := by
  let hother :=
    child_other_nonempty_of_card_ge_three hcard hir
  have heq :
      centreExponent
          ((C i).restrictDelete r hir hother) t =
        centreExponent (C i) t :=
    concrete_minimum_deletion_survivor_exponent_eq
      C hcard ht n hexp hover hchild r i hmin hir
  apply not_bothAdjacentPositive_of_no_unit_gain
    (C i) hir hother pre post hsplit ht
  rw [heq]
  omega

#print axioms concrete_minimum_deletion_survivor_exponent_eq
#print axioms concrete_minimum_deletion_column_rigidity
#print axioms minimum_deleted_ray_adjacent_zero_at_survivor
#print axioms minimum_deleted_ray_not_bothAdjacentPositive

end JSP000404Research
