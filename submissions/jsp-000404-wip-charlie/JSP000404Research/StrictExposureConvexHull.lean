import JSP000404Research.StrictSupportCone
import Mathlib.Analysis.Convex.Hull
import Mathlib.Analysis.Convex.Basic
import Mathlib.Tactic

/-!
# Strict exposure excludes membership in the convex hull of other points

A StrictlyExposedAt certificate gives a linear functional whose value is
strictly larger at every other point than at the exposed centre.  The open
half-space determined by this strict inequality is convex, so the convex hull
of any chosen collection of other points stays inside that half-space.  The
centre itself lies on the boundary and hence cannot belong to that hull.
-/

namespace JSP000404Research

theorem strictlyExposedAt_not_mem_convexHull_three
    {V : Type*} {p : V → Plane}
    {i a b c : V}
    (hia : a ≠ i)
    (hib : b ≠ i)
    (hic : c ≠ i)
    (hi : StrictlyExposedAt p i) :
    p i ∉ convexHull ℝ ({p a,p b,p c} : Set Plane) := by
  obtain ⟨u,hu⟩ := hi
  let f : Plane → ℝ := fun x => inner ℝ u x
  have hf : IsLinearMap ℝ f := by
    refine
      { map_add := ?_
        map_smul := ?_ }
    · intro x y
      simp [f, inner_add_right]
    · intro r x
      simp [f, inner_smul_right]
  let H : Set Plane := {x | f (p i) < f x}
  have hconv : Convex ℝ H := by
    simpa [H] using convex_halfSpace_gt hf (f (p i))
  have hsub :
      ({p a,p b,p c} : Set Plane) ⊆ H := by
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl
    · have h := hu a hia
      dsimp [H,f]
      rw [inner_sub_right] at h
      linarith
    · have h := hu b hib
      dsimp [H,f]
      rw [inner_sub_right] at h
      linarith
    · have h := hu c hic
      dsimp [H,f]
      rw [inner_sub_right] at h
      linarith
  intro hmem
  have hinside :
      p i ∈ H :=
    (convexHull_min hsub hconv) hmem
  exact (lt_irrefl (f (p i))) hinside

theorem four_strictlyExposed_convexHull_exclusions
    {V : Type*} {p : V → Plane}
    {a b c d : V}
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d)
    (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d)
    (ha : StrictlyExposedAt p a)
    (hb : StrictlyExposedAt p b)
    (hc : StrictlyExposedAt p c)
    (hd : StrictlyExposedAt p d) :
    p a ∉ convexHull ℝ ({p b,p c,p d} : Set Plane) ∧
    p b ∉ convexHull ℝ ({p a,p c,p d} : Set Plane) ∧
    p c ∉ convexHull ℝ ({p a,p b,p d} : Set Plane) ∧
    p d ∉ convexHull ℝ ({p a,p b,p c} : Set Plane) := by
  exact ⟨
    strictlyExposedAt_not_mem_convexHull_three
      hab.symm hac.symm had.symm ha,
    strictlyExposedAt_not_mem_convexHull_three
      hab hbc.symm hbd.symm hb,
    strictlyExposedAt_not_mem_convexHull_three
      hac hbc hcd.symm hc,
    strictlyExposedAt_not_mem_convexHull_three
      had hbd hcd hd
  ⟩

#print axioms strictlyExposedAt_not_mem_convexHull_three
#print axioms four_strictlyExposed_convexHull_exclusions

end JSP000404Research
