import JSP000404Research.ProjectionWeightedBlockHallReduction
import JSP000404Research.MinimalBlockDeficiency
import Mathlib.Tactic

/-!
# Every planar dyadic counterexample yields a connected canonical Hall core

The local candidate theorem supplies an actual retained completion cube
or an actual retained-active one-coordinate double cube at each centre.

If total dyadic weight exceeds the Boolean cube size, the weighted
candidate expansion must fail, yielding an inclusion-minimal deficient
family T of at least two centres.  Minimality forces ALL nontrivial
partitions of T to have a cross-part candidate intersection; equivalently,
the block intersection graph induced by T is connected.

This is a necessary structural consequence of a counterexample,
not a proof that the connected core cannot exist.  No global dyadic
conclusion or hole injection is asserted without that missing step.
-/

namespace JSP000404Research
namespace ProjectionOrdered

open OrderedEdgeColoring
open scoped BigOperators

theorem planar_overweight_forces_connected_nonsingleton_hall_core
    {V : Type*} [Fintype V]
    {p : V → Plane}
    (hp : Function.Injective p)
    {lam t delta : ℝ} {n : ℕ}
    (hcap : AngleCap p lam)
    (hn : 1 ≤ n)
    (hdelta0 : 0 ≤ delta)
    (hdeltaHalf : delta < (1 : ℝ) / 2)
    (ht : t = (n : ℝ) + delta)
    (hlam : lam = Real.pi / t)
    (C :
      letI : LinearOrder (ProjectionOrdered V) :=
        projectionLinearOrder hp
      ∀ i : ProjectionOrdered V,
        CentreProjectiveCycle (reindexedPoint_injective hp) i)
    (hover :
      letI : LinearOrder (ProjectionOrdered V) :=
        projectionLinearOrder hp
      2 ^ n < ∑ i : ProjectionOrdered V,
        2 ^ centreExponent (C i) t) :
    letI : LinearOrder (ProjectionOrdered V) :=
      projectionLinearOrder hp
    ∃ T : Finset (ProjectionOrdered V),
      2 ≤ T.card ∧
      BlockDeficient
        (fun i => 2 ^ centreExponent (C i) t)
        (planarLowerCandidateBlock
          hp hcap hn hdelta0 hdeltaHalf ht hlam C) T ∧
      ∀ A B : Finset (ProjectionOrdered V),
        A.Nonempty → B.Nonempty →
        Disjoint A B → A ∪ B = T →
        ¬ Disjoint
          (A.biUnion
            (planarLowerCandidateBlock
              hp hcap hn hdelta0 hdeltaHalf ht hlam C))
          (B.biUnion
            (planarLowerCandidateBlock
              hp hcap hn hdelta0 hdeltaHalf ht hlam C)) := by
  classical
  letI : LinearOrder (ProjectionOrdered V) :=
    projectionLinearOrder hp
  let demand : ProjectionOrdered V → ℕ :=
    fun i => 2 ^ centreExponent (C i) t
  let blocks : ProjectionOrdered V → Finset (Fin n → Bool) :=
    planarLowerCandidateBlock
      hp hcap hn hdelta0 hdeltaHalf ht hlam C
  obtain ⟨T, hTwo, hdef, hmin⟩ :=
    planar_lowerBranch_overweight_has_nontrivial_candidate_core
      hp hcap hn hdelta0 hdeltaHalf ht hlam C hover
  refine ⟨T, hTwo, hdef, ?_⟩
  intro A B hA hB hdisj hEq hcross
  exact minimal_deficient_no_noncross_partition
    demand blocks hdef hmin hA hB hdisj hEq hcross

#print axioms planar_overweight_forces_connected_nonsingleton_hall_core

end ProjectionOrdered
end JSP000404Research
