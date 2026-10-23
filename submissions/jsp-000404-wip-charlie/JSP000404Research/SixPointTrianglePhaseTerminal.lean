import JSP000404Research.SixPointHalfGridTriangleAvoidance
import Mathlib.Tactic

/-!
# Six-point ordinary triangle-phase terminal on the half-grid

This module retains the original three theorem names while reusing the
kernel-checked `OrdinaryShortTriangleBadAt` existential certificate.  The
previous attempted dependent `structure OrdinaryBadTriangleAt` did not
elaborate; its intended data and conditions were exactly those of the
existential ordinary short triangle predicate.

This is a conservative representation change: same original vertices, same
three normalized projective directions, same small arc and bad-phase bounds.
It does not include cyclic wrap triangles or prove the global Boolean-hole
payment.
-/

namespace JSP000404Research

/-- A concrete ordinary short-triangle bad-phase certificate. -/
abbrev OrdinaryBadTriangleAt
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane}
    (hp : Function.Injective p)
    (t delta x : ℝ) : Prop :=
  OrdinaryShortTriangleBadAt hp t delta x

theorem ordinaryBadTriangleAt_implies_criticalUnit
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane}
    {lam t delta x : ℝ}
    (hp : Function.Injective p)
    (hcap : AngleCap p lam)
    (C : ∀ v : V, CentreProjectiveCycle hp v)
    (ht : 0 < t)
    (hlam : lam = Real.pi / t)
    (hdeltaHalf : delta < (1 : ℝ) / 2)
    (B : OrdinaryBadTriangleAt hp t delta x) :
    ∃ u : GlobalUnitGapSlot C t,
      OrdinaryCriticalUnitBadAt C t delta u x := by
  exact ordinaryShortTriangleBadAt_implies_critical_unit
    hp hcap C ht hlam hdeltaHalf B

theorem exists_halfGrid_phase_without_ordinary_bad_triangle
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane}
    {lam t delta : ℝ} {n : ℕ}
    (hp : Function.Injective p)
    (hcap : AngleCap p lam)
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
    (hMin : ∀ i : V, i ≠ top →
      centreExponent (C i) t = n - 3) :
    ∃ r : Fin (2 * n + 1),
      ¬ OrdinaryBadTriangleAt hp t delta
          ((r.val : ℝ) / 2) := by
  exact six_point_exists_halfGrid_phase_avoiding_all_short_triangles
    hp hcap C hn4 hn5 hdelta0 hdeltaHalf ht hlam
    hcard top hTop hMin

theorem not_all_halfGrid_phases_have_ordinary_bad_triangle
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane}
    {lam t delta : ℝ} {n : ℕ}
    (hp : Function.Injective p)
    (hcap : AngleCap p lam)
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
    (hMin : ∀ i : V, i ≠ top →
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
