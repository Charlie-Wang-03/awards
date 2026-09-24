import JSP000404Research.CentreExponent
import Mathlib.Data.Finset.Dedup
import Mathlib.Data.List.Sort
import Mathlib.Tactic

/-!
# Centre exponent is independent of the sorted ray-cycle witness

A CentreProjectiveCycle is only a proof-carrying choice of one nondecreasing
enumeration of all non-centre vertices.

Two such cycles enumerate the same finite vertex set without repetition, hence
their ray lists are permutations.  Mapping rayThetaAt preserves permutation.
Since both resulting angle lists are nondecreasing, antisymmetry of the real
order makes the sorted permutation unique.

Therefore angles, cyclic normalized gaps, quotient lists, and centreExponent
are all independent of the chosen CentreProjectiveCycle witness.
-/

namespace JSP000404Research

namespace CentreProjectiveCycle

theorem rays_perm
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane} {hp : Function.Injective p} {i : V}
    (C D : CentreProjectiveCycle hp i) :
    C.rays.Perm D.rays := by
  classical
  apply List.perm_of_nodup_nodup_toFinset_eq
      C.nodup D.nodup
  rw [C.complete, D.complete]

theorem angles_perm
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane} {hp : Function.Injective p} {i : V}
    (C D : CentreProjectiveCycle hp i) :
    C.angles.Perm D.angles := by
  unfold angles
  exact (C.rays_perm D).map (rayThetaAt hp i)

theorem angles_eq
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane} {hp : Function.Injective p} {i : V}
    (C D : CentreProjectiveCycle hp i) :
    C.angles = D.angles := by
  exact (C.angles_perm D).eq_of_pairwise'
    C.angles_pairwise D.angles_pairwise

theorem gaps_eq
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane} {hp : Function.Injective p} {i : V}
    (C D : CentreProjectiveCycle hp i) :
    C.gaps = D.gaps := by
  unfold gaps
  rw [C.angles_eq D]

theorem quotientList_eq
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane} {hp : Function.Injective p} {i : V}
    (C D : CentreProjectiveCycle hp i)
    (t : ℝ) :
    quotientList t C.gaps =
      quotientList t D.gaps := by
  rw [C.gaps_eq D]

theorem centreQuotient_ext
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane} {hp : Function.Injective p} {i : V}
    (C D : CentreProjectiveCycle hp i)
    (t : ℝ) :
    HEq (centreQuotient C t)
      (centreQuotient D t) := by
  have hgap : C.gaps = D.gaps := C.gaps_eq D
  subst hgap
  rfl

theorem centreExponent_eq
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane} {hp : Function.Injective p} {i : V}
    (C D : CentreProjectiveCycle hp i)
    (t : ℝ) :
    centreExponent C t = centreExponent D t := by
  unfold centreExponent
  have hgap : C.gaps = D.gaps := C.gaps_eq D
  subst hgap
  rfl

theorem centreDeficit_eq
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane} {hp : Function.Injective p} {i : V}
    (C D : CentreProjectiveCycle hp i)
    (t : ℝ) (n : ℕ) :
    centreDeficit C t n = centreDeficit D t n := by
  unfold centreDeficit
  rw [C.centreExponent_eq D t]

#print axioms rays_perm
#print axioms angles_eq
#print axioms gaps_eq
#print axioms centreExponent_eq
#print axioms centreDeficit_eq

end CentreProjectiveCycle
end JSP000404Research
