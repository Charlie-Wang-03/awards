import JSP000404Research.TriangleCriticalUnitDomination
import JSP000404Research.OrdinaryCriticalHalfGrid
import Mathlib.Tactic

/-!
# Six-point triangle-phase terminal on the half grid

For the six-point top + five n-3 profile with n>=5, the previous modules give:

* at least one half-grid phase is not covered by any ordinary critical q=1
  transition obstruction;
* every ordinary short triangle bad arc containing a phase produces exactly
  such a concrete obstruction.

Therefore the half-grid phases cannot all admit ordinary short bad-triangle
certificates.

This theorem isolates the remaining geometric task of the fixed-phase route:
show that a phase whose merged wrap graph contains a triangle supplies the
ordinary lifted triangle certificate below (or its cyclic/wrap analogue).
-/

namespace JSP000404Research

open Real

/-- Data saying that one concrete triangle is bad at one real phase through an
ordinary lifted projective direction arc. -/
structure OrdinaryBadTriangleAt
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane}
    (hp : Function.Injective p)
    (t delta x : ℝ) : Prop where
  i j k : V
  hij : i ≠ j
  hik : i ≠ k
  hjk : j ≠ k
  L S : ℝ
  span_le : S ≤ 1 + delta
  ij_mem :
    L ≤ normalizedEdgeTheta hp t i j hij ∧
      normalizedEdgeTheta hp t i j hij ≤ L + S
  ik_mem :
    L ≤ normalizedEdgeTheta hp t i k hik ∧
      normalizedEdgeTheta hp t i k hik ≤ L + S
  jk_mem :
    L ≤ normalizedEdgeTheta hp t j k hjk ∧
      normalizedEdgeTheta hp t j k hjk ≤ L + S
  phase_mem :
    arcBadLeft L S ≤ x ∧
      x ≤ arcBadRight L delta

/-- Every ordinary bad-triangle certificate gives a concrete ordinary critical
unit obstruction at the same phase. -/
theorem ordinaryBadTriangleAt_implies_criticalUnit
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane} (hp : Function.Injective p)
    (hcap : AngleCap p lam)
    (C : ∀ v : V, CentreProjectiveCycle hp v)
    {lam t delta x : ℝ}
    (ht : 0 < t)
    (hlam : lam = Real.pi / t)
    (hdeltaHalf : delta < (1 : ℝ) / 2)
    (B : OrdinaryBadTriangleAt hp t delta x) :
    ∃ u : GlobalUnitGapSlot C t,
      OrdinaryCriticalUnitBadAt C t delta u x := by
  obtain ⟨u, _huCentre, hubad⟩ :=
    triangle_parent_bad_has_ordinary_critical_unit
      hp hcap C ht hlam hdeltaHalf B.span_le
      B.hij B.hik B.hjk
      B.ij_mem B.ik_mem B.jk_mem
      B.phase_mem
  exact ⟨u, hubad⟩

/-- Main n>=5 six-point terminal: not every half-grid phase can carry an
ordinary bad-triangle certificate. -/
theorem exists_halfGrid_phase_without_ordinary_bad_triangle
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane} (hp : Function.Injective p)
    (hcap : AngleCap p lam)
    {lam t delta : ℝ} {n : ℕ}
    (hn4 : 4 ≤ n)
    (hn5 : 5 ≤ n)
    (hdelta0 : 0 ≤ delta)
    (hdeltaHalf : delta < (1 : ℝ) / 2)
    (ht : t = (n : ℝ) + delta)
    (hlam : lam = Real.pi / t)
    (C : ∀ i : V, CentreProjectiveCycle hp i)
    (hcard : Fintype.card V = 6)
    (top : V)
    (hTop : centreExponent (C top) t = n - 1)
    (hMin :
      ∀ i : V, i ≠ top →
        centreExponent (C i) t = n - 3) :
    ∃ r : Fin (2 * n + 1),
      ¬ OrdinaryBadTriangleAt hp t delta
          ((r.val : ℝ) / 2) := by
  obtain ⟨r, hr⟩ :=
    exists_uncovered_halfGrid_phase_of_six_point_terminal
      C hn4 hn5 hdelta0 hdeltaHalf ht
      hcard top hTop hMin
  refine ⟨r, ?_⟩
  intro B
  have htpos :
      0 < t :=
    sendov_scale_pos (by omega : 1 ≤ n) hdelta0 ht
  obtain ⟨u, hubad⟩ :=
    ordinaryBadTriangleAt_implies_criticalUnit
      hp hcap C htpos hlam hdeltaHalf B
  exact hr u hubad

/-- Contradiction form convenient for a future rotating-wrap bridge. -/
theorem not_all_halfGrid_phases_have_ordinary_bad_triangle
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane} (hp : Function.Injective p)
    (hcap : AngleCap p lam)
    {lam t delta : ℝ} {n : ℕ}
    (hn4 : 4 ≤ n)
    (hn5 : 5 ≤ n)
    (hdelta0 : 0 ≤ delta)
    (hdeltaHalf : delta < (1 : ℝ) / 2)
    (ht : t = (n : ℝ) + delta)
    (hlam : lam = Real.pi / t)
    (C : ∀ i : V, CentreProjectiveCycle hp i)
    (hcard : Fintype.card V = 6)
    (top : V)
    (hTop : centreExponent (C top) t = n - 1)
    (hMin :
      ∀ i : V, i ≠ top →
        centreExponent (C i) t = n - 3) :
    ¬ (∀ r : Fin (2 * n + 1),
      OrdinaryBadTriangleAt hp t delta
        ((r.val : ℝ) / 2)) := by
  obtain ⟨r, hr⟩ :=
    exists_halfGrid_phase_without_ordinary_bad_triangle
      hp hcap hn4 hn5 hdelta0 hdeltaHalf
      ht hlam C hcard top hTop hMin
  intro hall
  exact hr (hall r)

#print axioms ordinaryBadTriangleAt_implies_criticalUnit
#print axioms exists_halfGrid_phase_without_ordinary_bad_triangle
#print axioms not_all_halfGrid_phases_have_ordinary_bad_triangle

end JSP000404Research
