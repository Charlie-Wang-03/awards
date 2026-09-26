import JSP000404Research.ExactMinimumDeletionCandidate
import JSP000404Research.ConcreteMinimumOverweightRigidity
import Mathlib.Tactic

/-!
# Two minimum deletion columns force two zero-adjacent rays at every common survivor

The exact-minimum induction route eventually produces two distinct minimum
centres r,s outside a fixed exact maximum-angle witness triple.  Each of the
two one-vertex children is bounded by the inductive 2^n estimate.

ConcreteMinimumOverweightRigidity already shows that one bounded deletion of a
minimum centre is completely rigid at every survivor: the survivor exponent
does not increase, hence the deleted ray has a zero quotient on at least one
of its two cyclic sides.

This file packages the simultaneous consequence for two distinct minimum
centres.  The resulting endpoint is purely local:

  at every common survivor i, the ray i->r and the ray i->s are both
  zero-adjacent in the parent projective quotient cycle.

No new extremal-profile assumption is introduced.
-/

namespace JSP000404Research

/-- Local zero-adjacency predicate for the ray from survivor i to a deleted
vertex r, expressed in the exact split format used by the concrete deletion
lemmas. -/
def DeletedRayAdjacentZero
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane} {hp : Function.Injective p}
    (C : ∀ i : V, CentreProjectiveCycle hp i)
    (t : ℝ)
    (r i : V)
    (hir : i ≠ r) : Prop :=
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
              Real.pi)) = 0

/-- Two individually bounded minimum-deletion children force zero adjacency of
both deleted rays at every common survivor. -/
theorem two_minimum_child_bounds_force_two_deletedRayAdjacentZero
    {V : Type*} [LinearOrder V] [Fintype V] [Nonempty V]
    {p : V → Plane} {hp : Function.Injective p}
    (C : ∀ i : V, CentreProjectiveCycle hp i)
    (hcard : 3 ≤ Fintype.card V)
    {t : ℝ}
    (ht : 0 ≤ t)
    (n : ℕ)
    (r0 r s i : V)
    (hexp :
      ∀ j : V, centreExponent (C j) t ≤ n)
    (hover :
      2 ^ n < ∑ j : V, 2 ^ centreExponent (C j) t)
    (hmin :
      ∀ j : V,
        centreExponent (C r0) t ≤
          centreExponent (C j) t)
    (hrMin :
      centreExponent (C r) t =
        centreExponent (C r0) t)
    (hsMin :
      centreExponent (C s) t =
        centreExponent (C r0) t)
    (hchildR :
      deletionPostWeight
          (concreteDeletionAfter C hcard t) r
        ≤ 2 ^ n)
    (hchildS :
      deletionPostWeight
          (concreteDeletionAfter C hcard t) s
        ≤ 2 ^ n)
    (hir : i ≠ r)
    (his : i ≠ s) :
    DeletedRayAdjacentZero C t r i hir ∧
      DeletedRayAdjacentZero C t s i his := by
  have hminR :
      ∀ j : V,
        centreExponent (C r) t ≤
          centreExponent (C j) t := by
    intro j
    rw [hrMin]
    exact hmin j
  have hminS :
      ∀ j : V,
        centreExponent (C s) t ≤
          centreExponent (C j) t := by
    intro j
    rw [hsMin]
    exact hmin j
  constructor
  · exact
      minimum_deleted_ray_adjacent_zero_at_survivor_of_child_bound
        C hcard ht n r i hexp hover hchildR hminR hir
  · exact
      minimum_deleted_ray_adjacent_zero_at_survivor_of_child_bound
        C hcard ht n s i hexp hover hchildS hminS his

/-- Exact-witness large-minimum-layer package.

If an overweight exact-normalized counterexample has more than three minimum
vertices and every witness-avoiding minimum child satisfies the inductive
bound, then there are two distinct witness-avoiding minima r,s such that:

* both one-vertex deletions preserve the exact normalization;
* both root deletion columns are rigid;
* at every common survivor, both rays to r and s are zero-adjacent.

This isolates the remaining large-minimum-layer obstruction as a local planar
incidence problem. -/
theorem exists_two_exact_minima_with_common_survivor_zero_adjacency
    {V : Type*} [LinearOrder V] [Fintype V] [Nonempty V]
    {p : V → Plane} {hp : Function.Injective p}
    {lam t : ℝ}
    (hcap : AngleCap p lam)
    (W : ExactAngleWitness p lam)
    (C : ∀ i : V, CentreProjectiveCycle hp i)
    (hV : 3 ≤ Fintype.card V)
    (ht0 : 0 ≤ t)
    (n : ℕ)
    (r0 : V)
    (hexp :
      ∀ i : V, centreExponent (C i) t ≤ n)
    (hminStrict :
      centreExponent (C r0) t < n)
    (hover :
      2 ^ n < ∑ i : V, 2 ^ centreExponent (C i) t)
    (hmin :
      ∀ i : V,
        centreExponent (C r0) t ≤
          centreExponent (C i) t)
    (hminCard :
      3 <
        (minimumExponentVertices
          (fun i => centreExponent (C i) t) r0).card)
    (hchild :
      ∀ r : V,
        r ≠ W.a → r ≠ W.b → r ≠ W.c →
        deletionPostWeight
            (concreteDeletionAfter C hV t) r
          ≤ 2 ^ n) :
    ∃ r s : V,
      r ≠ s ∧
      centreExponent (C r) t =
        centreExponent (C r0) t ∧
      centreExponent (C s) t =
        centreExponent (C r0) t ∧
      r ≠ W.a ∧ r ≠ W.b ∧ r ≠ W.c ∧
      s ≠ W.a ∧ s ≠ W.b ∧ s ≠ W.c ∧
      ExactAngleCap (deletePoint p r) lam ∧
      ExactAngleCap (deletePoint p s) lam ∧
      deletionPostWeight
          (concreteDeletionAfter C hV t) r = 2 ^ n ∧
      deletionPostWeight
          (concreteDeletionAfter C hV t) s = 2 ^ n ∧
      (∀ j : V, j ≠ r →
        concreteDeletionAfter C hV t r j =
          centreExponent (C j) t) ∧
      (∀ j : V, j ≠ s →
        concreteDeletionAfter C hV t s j =
          centreExponent (C j) t) ∧
      ∀ i : V, i ≠ r → i ≠ s →
        DeletedRayAdjacentZero C t r i (by assumption) ∧
          DeletedRayAdjacentZero C t s i (by assumption) := by
  obtain ⟨r, s, hrs, hrMin, hsMin,
      hra, hrb, hrc, hsa, hsb, hsc,
      hexactR, hexactS,
      hpostR, hpostS, hrigR, hrigS⟩ :=
    exists_two_exact_minima_with_root_rigidity
      hcap W C hV ht0 n r0 hexp hminStrict
      hover hmin hminCard hchild
  refine ⟨r, s, hrs, hrMin, hsMin,
    hra, hrb, hrc, hsa, hsb, hsc,
    hexactR, hexactS,
    hpostR, hpostS, hrigR, hrigS, ?_⟩
  intro i hir his
  exact
    two_minimum_child_bounds_force_two_deletedRayAdjacentZero
      C hV ht0 n r0 r s i
      hexp hover hmin hrMin hsMin
      (by simpa [hpostR])
      (by simpa [hpostS])
      hir his

#print axioms two_minimum_child_bounds_force_two_deletedRayAdjacentZero
#print axioms exists_two_exact_minima_with_common_survivor_zero_adjacency

end JSP000404Research
