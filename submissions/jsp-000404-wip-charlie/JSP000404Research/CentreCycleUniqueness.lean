
import JSP000404Research.CentreExponent
import Mathlib.Data.List.Sort
import Mathlib.Tactic

/-!
# Canonical centre-cycle exponent is independent of the cycle witness

A CentreProjectiveCycle contains every non-centre vertex exactly once and is
sorted by the canonical projective parameter rayThetaAt.

Two such cycles therefore differ only by the order of vertices having equal
theta.  After mapping to angles, both lists are sorted permutations of the
same multiset of real values, hence are equal.

Consequently their normalized cyclic gap lists, quotient lists, and
centreExponent values are identical.

This permits later geometric constructions to choose whichever canonical
cycle is most convenient without changing the Sendov exponent.
-/

namespace JSP000404Research

theorem centreCycle_rays_perm
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane} {hp : Function.Injective p} {i : V}
    (C₁ C₂ : CentreProjectiveCycle hp i) :
    C₁.rays ~ C₂.rays := by
  classical
  apply (List.perm_ext_iff_of_nodup C₁.nodup C₂.nodup).2
  intro j
  constructor <;> intro hj
  · have hjFin : j ∈ C₁.rays.toFinset := by simpa using hj
    rw [C₁.complete] at hjFin
    have : j ∈ C₂.rays.toFinset := by
      rw [C₂.complete]
      simpa using hjFin
    simpa using this
  · have hjFin : j ∈ C₂.rays.toFinset := by simpa using hj
    rw [C₂.complete] at hjFin
    have : j ∈ C₁.rays.toFinset := by
      rw [C₁.complete]
      simpa using hjFin
    simpa using this

theorem centreCycle_angles_perm
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane} {hp : Function.Injective p} {i : V}
    (C₁ C₂ : CentreProjectiveCycle hp i) :
    C₁.angles ~ C₂.angles := by
  unfold CentreProjectiveCycle.angles
  exact (centreCycle_rays_perm C₁ C₂).map
    (rayThetaAt hp i)

theorem centreCycle_angles_eq
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane} {hp : Function.Injective p} {i : V}
    (C₁ C₂ : CentreProjectiveCycle hp i) :
    C₁.angles = C₂.angles := by
  exact List.Perm.eq_of_pairwise'
    C₁.angles_pairwise
    C₂.angles_pairwise
    (centreCycle_angles_perm C₁ C₂)

theorem centreCycle_gaps_eq
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane} {hp : Function.Injective p} {i : V}
    (C₁ C₂ : CentreProjectiveCycle hp i) :
    C₁.gaps = C₂.gaps := by
  unfold CentreProjectiveCycle.gaps
  rw [centreCycle_angles_eq C₁ C₂]

theorem centreQuotientList_eq_of_cycles
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane} {hp : Function.Injective p} {i : V}
    (C₁ C₂ : CentreProjectiveCycle hp i)
    (t : ℝ) :
    quotientList t C₁.gaps =
      quotientList t C₂.gaps := by
  rw [centreCycle_gaps_eq C₁ C₂]

theorem centreExponent_eq_of_cycles
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane} {hp : Function.Injective p} {i : V}
    (C₁ C₂ : CentreProjectiveCycle hp i)
    (t : ℝ) :
    centreExponent C₁ t = centreExponent C₂ t := by
  rw [← listExponent_quotientList_eq_centreExponent' C₁ t,
      ← listExponent_quotientList_eq_centreExponent' C₂ t,
      centreQuotientList_eq_of_cycles C₁ C₂ t]

#print axioms centreCycle_rays_perm
#print axioms centreCycle_angles_eq
#print axioms centreCycle_gaps_eq
#print axioms centreExponent_eq_of_cycles

end JSP000404Research
