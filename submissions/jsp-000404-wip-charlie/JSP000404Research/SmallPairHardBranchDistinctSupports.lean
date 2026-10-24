import JSP000404Research.SmallTriangleApexUniqueness
import JSP000404Research.SixPointHardLowSupportGeometry
import Mathlib.Tactic

/-!
# Genuine hard-branch small-pair witnesses use different original triangles

In the pure two-minimum branch, two distinct source centres each own an
actual small-angle triangle. The same unordered original triangle cannot
serve both centres, by the kernel-certified small-angle apex uniqueness.

No Boolean true-hole, dyadic-surplus credit or global charge is inferred.
-/

namespace JSP000404Research

/-- Actual away-from-top small pair witnesses at DISTINCT source centres
cannot reuse the SAME unordered set of three original vertices. -/
theorem small_pair_away_from_top_distinct_triangle_supports
    {V : Type*} [DecidableEq V]
    {p : V → Plane} (hp : Function.Injective p)
    {delta lam : ℝ}
    (hcap : AngleCap p lam)
    (hdeltaHalf : delta < (1 : ℝ) / 2)
    (hlampos : 0 < lam)
    (top i j : V)
    (hij : i ≠ j)
    (hi : Nonempty (SmallPairAwayFromTop (p := p) top i delta lam))
    (hj : Nonempty (SmallPairAwayFromTop (p := p) top j delta lam)) :
    ∃ (wi : SmallPairAwayFromTop (p := p) top i delta lam)
      (wj : SmallPairAwayFromTop (p := p) top j delta lam),
      ({i, wi.x.1, wi.y.1} : Finset V) ≠
        ({j, wj.x.1, wj.y.1} : Finset V) := by
  obtain ⟨wi⟩ := hi
  obtain ⟨wj⟩ := hj
  refine ⟨wi, wj, ?_⟩
  intro heq
  have hxy_i : wi.x.1 ≠ wi.y.1 := by
    intro h
    exact wi.x_ne_y (Subtype.ext h)
  have hxy_j : wj.x.1 ≠ wj.y.1 := by
    intro h
    exact wj.x_ne_y (Subtype.ext h)
  have hsame : i = j :=
    actual_small_triangle_apex_unique_of_same_support
      hp hcap hdeltaHalf hlampos
      wi.x.2.symm wi.y.2.symm hxy_i
      wj.x.2.symm wj.y.2.symm hxy_j
      wi.small wj.small heq
  exact hij hsame

#print axioms small_pair_away_from_top_distinct_triangle_supports

end JSP000404Research
