import JSP000404Research.DirectionDataGlobalOverweightRigidity
import JSP000404Research.ProjectionCutLocalCycle
import Mathlib.Tactic

/-!
# A planar overweight configuration has a concrete rigid local ray cycle

This uses the actual canonical generic projection, not an arbitrary abstract
DirectionData realization. Genuine planar centre exponents equal exponents of
the cut/rotated direction cycles. The sorry-free global-overweight rigidity
theorem therefore transfers to the planar AngleCap source.

The disjunction remains an open geometric obstacle, not a contradiction.
It makes no subset-wise Hall-G1 assumption and requires no delta<1/2
restriction beyond the width t<n+1.
-/

namespace JSP000404Research
namespace ProjectionOrdered

open DirectionData

/-- Any truly overweight planar AngleCap configuration admits a canonical
projection centre exhibiting either a short band-crossing adjacent ray pair
or all-step cyclic gap rigidity. The existential witness refers to the
*actual* cut/rotated local DirectionData cycle. -/
theorem planar_overweight_has_canonical_local_rigid_witness
    {V : Type*} [Fintype V]
    {p : V → Plane}
    (hp : Function.Injective p)
    {lam t : ℝ} {n : ℕ}
    (hcap : AngleCap p lam)
    (htpos : 0 < t)
    (hlam : lam = Real.pi / t)
    (hwidth : t < (n : ℝ) + 1)
    (cycles :
      letI : LinearOrder (ProjectionOrdered V) :=
        projectionLinearOrder hp
      ∀ i : ProjectionOrdered V,
        CentreProjectiveCycle (reindexedPoint_injective hp) i)
    (hover :
      letI : LinearOrder (ProjectionOrdered V) :=
        projectionLinearOrder hp
      2 ^ n < ∑ i : ProjectionOrdered V,
        2 ^ centreExponent (cycles i) t) :
    letI : LinearOrder (ProjectionOrdered V) :=
      projectionLinearOrder hp
    let D := genericDirectionData_sendov hp hcap htpos hlam
    let C : ∀ i : ProjectionOrdered V, LocalDirectionCycle D i :=
      fun i => projectionCutLocalCycle hp hcap htpos hlam i (cycles i)
    (
      ∃ (i : ProjectionOrdered V), ∃ (u v : OtherVertex i)
        (pre post : List (OtherVertex i)),
        (C i).rays = pre ++ u :: v :: post ∧
        0 ≤ D.localDirectionValue i v - D.localDirectionValue i u ∧
        D.localDirectionValue i v - D.localDirectionValue i u < 1 ∧
        Nat.floor (D.localDirectionValue i v) -
          Nat.floor (D.localDirectionValue i u) = 1
    ) ∨
    (
      ∃ i : ProjectionOrdered V, ∃ a : ℝ, ∃ xs : List ℝ,
        (C i).values = a :: xs ∧
        InteriorBandGapTight a xs ∧
        excess (Nat.floor (a + t - xs.getLastD a)) =
          n - Nat.floor (xs.getLastD a) + Nat.floor a
    ) := by
  classical
  letI : LinearOrder (ProjectionOrdered V) := projectionLinearOrder hp
  let D : DirectionData (ProjectionOrdered V) t :=
    genericDirectionData_sendov hp hcap htpos hlam
  let C : ∀ i : ProjectionOrdered V, LocalDirectionCycle D i :=
    fun i => projectionCutLocalCycle hp hcap htpos hlam i (cycles i)
  have hExp : ∀ i : ProjectionOrdered V,
      (C i).exponent = centreExponent (cycles i) t := by
    intro i
    exact projectionCutLocalCycle_exponent_eq_centreExponent
      hp hcap htpos hlam i (cycles i)
  have hoverLocal :
      2 ^ n < ∑ i : ProjectionOrdered V, 2 ^ (C i).exponent := by
    calc
      2 ^ n < ∑ i : ProjectionOrdered V,
          2 ^ centreExponent (cycles i) t := hover
      _ = ∑ i : ProjectionOrdered V, 2 ^ (C i).exponent := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [hExp i]
  exact overweight_directionData_has_rigid_local_witness
    D hwidth C hoverLocal

#print axioms planar_overweight_has_canonical_local_rigid_witness

end ProjectionOrdered
end JSP000404Research
