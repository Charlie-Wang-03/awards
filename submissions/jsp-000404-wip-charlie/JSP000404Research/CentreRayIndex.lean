
import JSP000404Research.CentreProjectiveCycle
import Mathlib.Data.List.NodupEquivFin
import Mathlib.Data.List.Pairwise
import Mathlib.Tactic

/-!
# Canonical indices in a centre's sorted projective ray list

A CentreProjectiveCycle lists every OtherVertex exactly once.  Its nodup and
completeness fields therefore give an equivalence

  Fin C.rays.length ≃ OtherVertex i.

We use the inverse equivalence as the canonical ray index.

Because C.rays is theta-sorted, strict projective-angle order forces strict
index order.  This provides a convenient finite-order interface for exact
witness adjacency and later multi-deletion arguments.
-/

namespace JSP000404Research
namespace CentreProjectiveCycle

noncomputable def rayEquiv
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane} {hp : Function.Injective p} {i : V}
    (C : CentreProjectiveCycle hp i) :
    Fin C.rays.length ≃ OtherVertex i := by
  classical
  exact C.nodup.getEquivOfForallMemList
    C.rays C.nodup (fun j => C.mem_rays_iff j)

noncomputable def rayIndex
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane} {hp : Function.Injective p} {i : V}
    (C : CentreProjectiveCycle hp i)
    (j : OtherVertex i) :
    Fin C.rays.length :=
  (C.rayEquiv).symm j

@[simp] theorem get_rayIndex
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane} {hp : Function.Injective p} {i : V}
    (C : CentreProjectiveCycle hp i)
    (j : OtherVertex i) :
    C.rays.get (C.rayIndex j) = j := by
  change C.rayEquiv (C.rayIndex j) = j
  exact Equiv.apply_symm_apply C.rayEquiv j

@[simp] theorem rayIndex_get
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane} {hp : Function.Injective p} {i : V}
    (C : CentreProjectiveCycle hp i)
    (q : Fin C.rays.length) :
    C.rayIndex (C.rays.get q) = q := by
  change (C.rayEquiv).symm (C.rayEquiv q) = q
  exact Equiv.symm_apply_apply C.rayEquiv q

theorem rayIndex_injective
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane} {hp : Function.Injective p} {i : V}
    (C : CentreProjectiveCycle hp i) :
    Function.Injective C.rayIndex := by
  intro j k h
  have :=
    congrArg (fun q => C.rays.get q) h
  simpa using this

theorem rayIndex_ne_of_ne
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane} {hp : Function.Injective p} {i : V}
    (C : CentreProjectiveCycle hp i)
    {j k : OtherVertex i}
    (hjk : j ≠ k) :
    C.rayIndex j ≠ C.rayIndex k := by
  exact fun h => hjk (C.rayIndex_injective h)

/-- Strict theta order forces strict list-index order. -/
theorem rayIndex_lt_of_theta_lt
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane} {hp : Function.Injective p} {i : V}
    (C : CentreProjectiveCycle hp i)
    {j k : OtherVertex i}
    (htheta :
      rayThetaAt hp i j < rayThetaAt hp i k) :
    C.rayIndex j < C.rayIndex k := by
  have hne :
      C.rayIndex j ≠ C.rayIndex k := by
    intro hidx
    have hget :=
      congrArg (fun q => C.rays.get q) hidx
    have hjk : j = k := by
      simpa using hget
    subst k
    exact (lt_irrefl _) htheta
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · exact hlt
  · have hrel :=
      C.theta_sorted.rel_get_of_lt hgt
    rw [C.get_rayIndex, C.get_rayIndex] at hrel
    exact False.elim ((not_lt_of_ge hrel) htheta)

/-- Weak index order gives weak theta order. -/
theorem theta_le_of_rayIndex_le
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane} {hp : Function.Injective p} {i : V}
    (C : CentreProjectiveCycle hp i)
    {j k : OtherVertex i}
    (hidx : C.rayIndex j ≤ C.rayIndex k) :
    rayThetaAt hp i j ≤ rayThetaAt hp i k := by
  by_cases hEq : C.rayIndex j = C.rayIndex k
  · have hjk : j = k := C.rayIndex_injective hEq
    simp [hjk]
  · have hlt : C.rayIndex j < C.rayIndex k :=
      lt_of_le_of_ne hidx hEq
    have hrel :=
      C.theta_sorted.rel_get_of_lt hlt
    simpa using hrel

/-- Strict index order implies weak theta order. -/
theorem theta_le_of_rayIndex_lt
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane} {hp : Function.Injective p} {i : V}
    (C : CentreProjectiveCycle hp i)
    {j k : OtherVertex i}
    (hidx : C.rayIndex j < C.rayIndex k) :
    rayThetaAt hp i j ≤ rayThetaAt hp i k :=
  C.theta_le_of_rayIndex_le hidx.le

#print axioms get_rayIndex
#print axioms rayIndex_lt_of_theta_lt
#print axioms theta_le_of_rayIndex_le

end CentreProjectiveCycle
end JSP000404Research
