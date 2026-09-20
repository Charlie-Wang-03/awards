import JSP000404Research.CyclicProjectiveGaps
import Mathlib.Tactic

/-!
# A concrete projective ray cycle around a finite planar centre

A CentreProjectiveCycle is an angularly sorted enumeration of every vertex
other than the chosen centre.  The actual radius, sign and projective angle of
each listed ray are the canonical functions from FiniteProjectiveRays.

From the ordered ray list we derive:

* the angle list in [0,pi),
* the sign list,
* the positive radii,
* the normalized cyclic projective gaps.

For a nontrivial centre the normalized gaps are nonnegative, have the same
length as the ray list, and sum exactly to one.
-/

namespace JSP000404Research

open Real

structure CentreProjectiveCycle
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane}
    (hp : Function.Injective p)
    (i : V) where
  rays : List (OtherVertex i)
  complete : rays.toFinset = Finset.univ
  nodup : rays.Nodup
  nonempty : rays ≠ []
  theta_sorted :
    rays.Pairwise
      (fun a b =>
        rayThetaAt hp i a ≤ rayThetaAt hp i b)

namespace CentreProjectiveCycle

def angles
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane} {hp : Function.Injective p} {i : V}
    (C : CentreProjectiveCycle hp i) : List ℝ :=
  C.rays.map (rayThetaAt hp i)

def signs
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane} {hp : Function.Injective p} {i : V}
    (C : CentreProjectiveCycle hp i) : List Bool :=
  C.rays.map (raySignAt hp i)

def radii
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane} {hp : Function.Injective p} {i : V}
    (C : CentreProjectiveCycle hp i) : List ℝ :=
  C.rays.map (rayRhoAt hp i)

def gaps
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane} {hp : Function.Injective p} {i : V}
    (C : CentreProjectiveCycle hp i) : List ℝ :=
  normalizedProjectiveGaps C.angles

theorem angles_length
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane} {hp : Function.Injective p} {i : V}
    (C : CentreProjectiveCycle hp i) :
    C.angles.length = C.rays.length := by
  simp [angles]

theorem signs_length
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane} {hp : Function.Injective p} {i : V}
    (C : CentreProjectiveCycle hp i) :
    C.signs.length = C.rays.length := by
  simp [signs]

theorem gaps_length
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane} {hp : Function.Injective p} {i : V}
    (C : CentreProjectiveCycle hp i) :
    C.gaps.length = C.rays.length := by
  rw [gaps, normalizedProjectiveGaps_length, angles_length]

theorem angles_nonempty
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane} {hp : Function.Injective p} {i : V}
    (C : CentreProjectiveCycle hp i) :
    C.angles ≠ [] := by
  simp [angles, C.nonempty]

theorem angles_pairwise
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane} {hp : Function.Injective p} {i : V}
    (C : CentreProjectiveCycle hp i) :
    C.angles.Pairwise (· ≤ ·) := by
  rw [angles, List.pairwise_map]
  exact C.theta_sorted

theorem angle_mem_bounds
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane} {hp : Function.Injective p} {i : V}
    (C : CentreProjectiveCycle hp i)
    {theta : ℝ} (htheta : theta ∈ C.angles) :
    0 ≤ theta ∧ theta < Real.pi := by
  rw [angles, List.mem_map] at htheta
  obtain ⟨j, _, rfl⟩ := htheta
  exact ⟨rayThetaAt_nonneg hp i j, rayThetaAt_lt_pi hp i j⟩

theorem radii_pos
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane} {hp : Function.Injective p} {i : V}
    (C : CentreProjectiveCycle hp i)
    {rho : ℝ} (hrho : rho ∈ C.radii) :
    0 < rho := by
  rw [radii, List.mem_map] at hrho
  obtain ⟨j, _, rfl⟩ := hrho
  exact rayRhoAt_pos hp i j

/-- Every listed ray retains its exact geometric displacement representation. -/
theorem ray_representation
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane} {hp : Function.Injective p} {i : V}
    (C : CentreProjectiveCycle hp i)
    {j : OtherVertex i} (hj : j ∈ C.rays) :
    p j.1 - p i =
      rayRhoAt hp i j •
        signedRayDirection (raySignAt hp i j) (rayThetaAt hp i j) := by
  exact rayRepAt_eq hp i j

theorem gaps_sum
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane} {hp : Function.Injective p} {i : V}
    (C : CentreProjectiveCycle hp i) :
    C.gaps.sum = 1 := by
  obtain ⟨a, xs, hangles⟩ : ∃ a xs, C.angles = a :: xs := by
    cases h : C.angles with
    | nil => exact False.elim (C.angles_nonempty h)
    | cons a xs => exact ⟨a, xs, h⟩
  rw [gaps, hangles]
  exact normalizedProjectiveGaps_sum

theorem gaps_nonneg
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane} {hp : Function.Injective p} {i : V}
    (C : CentreProjectiveCycle hp i) :
    ∀ g ∈ C.gaps, 0 ≤ g := by
  obtain ⟨a, xs, hangles⟩ : ∃ a xs, C.angles = a :: xs := by
    cases h : C.angles with
    | nil => exact False.elim (C.angles_nonempty h)
    | cons a xs => exact ⟨a, xs, h⟩
  have haMem : a ∈ C.angles := by
    rw [hangles]
    simp
  have ha0 := (C.angle_mem_bounds haMem).1
  have hsorted : (a :: xs).Pairwise (· ≤ ·) := by
    simpa [hangles] using C.angles_pairwise
  have hall : ∀ theta ∈ a :: xs, theta < Real.pi := by
    intro theta htheta
    exact (C.angle_mem_bounds (by simpa [hangles] using htheta)).2
  rw [gaps, hangles]
  exact normalizedProjectiveGaps_nonneg a xs ha0 hsorted hall

/-- Every non-centre vertex occurs exactly once in the ray cycle. -/
theorem mem_rays_iff
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane} {hp : Function.Injective p} {i : V}
    (C : CentreProjectiveCycle hp i)
    (j : OtherVertex i) :
    j ∈ C.rays := by
  have : j ∈ C.rays.toFinset := by
    rw [C.complete]
    simp
  simpa using this

end CentreProjectiveCycle

/-- Every centre with at least one other vertex admits such a projective cycle. -/
theorem exists_centreProjectiveCycle
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane}
    (hp : Function.Injective p)
    (i : V)
    (hother : Nonempty (OtherVertex i)) :
    Nonempty (CentreProjectiveCycle hp i) := by
  classical
  obtain ⟨rays, hcomplete, hnodup, hsorted⟩ :=
    exists_theta_sorted_other_vertices hp i
  have hne : rays ≠ [] := by
    obtain ⟨j⟩ := hother
    intro hrays
    subst rays
    have hj : j ∈ (Finset.univ : Finset (OtherVertex i)) := by simp
    rw [← hcomplete] at hj
    simp at hj
  exact ⟨
    { rays := rays
      complete := hcomplete
      nodup := hnodup
      nonempty := hne
      theta_sorted := hsorted }⟩

#print axioms CentreProjectiveCycle.gaps_sum
#print axioms CentreProjectiveCycle.gaps_nonneg
#print axioms exists_centreProjectiveCycle

end JSP000404Research
