import JSP000404Research.GenericLineBlocks
import JSP000404Research.ProjectiveCutRotation
import JSP000404Research.CentreListExponent
import Mathlib.Tactic

/-!
# Centre exponent is invariant under the generic projection cut

Around a projection-ordered centre, let

  neg = generic line angles below 0,
  non = generic line angles at least 0.

The generic projective cut has angle order

  neg ++ non.

The canonical [0,pi) cut has angle order

  non ++ (neg shifted by +pi),

which is exactly the angle list of genericCanonicalCycle.

If both blocks are nonempty, ProjectiveCutRotation says the cyclic gap lists
differ by a rotation.  If one block is empty, the two lists are either equal or
differ by one common +pi translation.

Therefore the quotient-list exponent is the same at both cuts.  By
CentreCycleChoiceInvariant, this equals the centreExponent of every canonical
CentreProjectiveCycle witness at the same centre.
-/

namespace JSP000404Research
namespace ProjectionOrdered

noncomputable def genericNegativeAngles
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane}
    (hp : Function.Injective p)
    (i : ProjectionOrdered V) : List ℝ :=
  (genericNegativeRays hp i).map
    (genericLineAngleAt hp i)

noncomputable def genericNonnegativeAngles
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane}
    (hp : Function.Injective p)
    (i : ProjectionOrdered V) : List ℝ :=
  (genericNonnegativeRays hp i).map
    (genericLineAngleAt hp i)

noncomputable def genericCutAngles
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane}
    (hp : Function.Injective p)
    (i : ProjectionOrdered V) : List ℝ :=
  genericNegativeAngles hp i ++
    genericNonnegativeAngles hp i

theorem genericCanonicalCycle_angles
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane}
    (hp : Function.Injective p)
    (i : ProjectionOrdered V)
    (hother : Nonempty (OtherVertex i.toOriginal)) :
    (genericCanonicalCycle hp i hother).angles =
      genericNonnegativeAngles hp i ++
        (genericNegativeAngles hp i).map
          (fun x => x + Real.pi) := by
  change
    (genericCanonicalRays hp i).map
        (rayThetaAt hp i.toOriginal)
      =
    genericNonnegativeAngles hp i ++
      (genericNegativeAngles hp i).map
        (fun x => x + Real.pi)
  rw [genericCanonicalRays, List.map_append]
  congr 1
  · unfold genericNonnegativeAngles
    apply List.map_congr_left
    intro j hj
    exact canonicalTheta_eq_generic_of_nonnegative_mem
      hp i hj
  · unfold genericNegativeAngles
    rw [List.map_map]
    apply List.map_congr_left
    intro j hj
    exact canonicalTheta_eq_generic_add_pi_of_negative_mem
      hp i hj

theorem genericCanonicalCycle_angles_eq_after_cut
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane}
    (hp : Function.Injective p)
    (i : ProjectionOrdered V)
    (hother : Nonempty (OtherVertex i.toOriginal)) :
    (genericCanonicalCycle hp i hother).angles =
      anglesAfterProjectiveCut
        0
        (genericNegativeAngles hp i)
        (genericNonnegativeAngles hp i) := by
  rw [genericCanonicalCycle_angles hp i hother]
  simp [anglesAfterProjectiveCut]

/-- Generic and canonical gap lists agree up to a cyclic rotation. -/
theorem exists_genericCanonical_gap_rotation
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane}
    (hp : Function.Injective p)
    (i : ProjectionOrdered V)
    (hother : Nonempty (OtherVertex i.toOriginal)) :
    ∃ r : ℕ,
      (genericCanonicalCycle hp i hother).gaps =
        (normalizedProjectiveGaps
          (genericCutAngles hp i)).rotate r := by
  let neg := genericNegativeAngles hp i
  let non := genericNonnegativeAngles hp i
  have hcanon :
      (genericCanonicalCycle hp i hother).angles =
        anglesAfterProjectiveCut 0 neg non := by
    simpa [neg, non] using
      genericCanonicalCycle_angles_eq_after_cut
        hp i hother
  cases hneg : neg with
  | nil =>
      refine ⟨0, ?_⟩
      unfold CentreProjectiveCycle.gaps
      rw [hcanon]
      simp [anglesAfterProjectiveCut,
        genericCutAngles, neg, non, hneg]
  | cons a as =>
      cases hnon : non with
      | nil =>
          refine ⟨0, ?_⟩
          unfold CentreProjectiveCycle.gaps
          rw [hcanon]
          have htrans :=
            normalizedProjectiveGaps_map_add
              a Real.pi as
          simpa [anglesAfterProjectiveCut,
            genericCutAngles, neg, non,
            hneg, hnon, Function.comp_def] using htrans
      | cons b bs =>
          refine ⟨(a :: as).length, ?_⟩
          unfold CentreProjectiveCycle.gaps
          rw [hcanon]
          have hrot :=
            normalizedProjectiveGaps_after_cut_eq_rotate
              0 a b as bs
          simpa [genericCutAngles, neg, non,
            hneg, hnon, anglesAfterProjectiveCut] using hrot

/-- Quotient-list exponent at the canonical cycle equals that at the generic
line-angle cut. -/
theorem genericCanonical_exponent_eq_genericCut
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane}
    (hp : Function.Injective p)
    (i : ProjectionOrdered V)
    (hother : Nonempty (OtherVertex i.toOriginal))
    (t : ℝ) :
    centreExponent (genericCanonicalCycle hp i hother) t =
      listExponent
        (quotientList t
          (normalizedProjectiveGaps
            (genericCutAngles hp i))) := by
  rw [centreExponent_eq_listExponent]
  obtain ⟨r, hrot⟩ :=
    exists_genericCanonical_gap_rotation hp i hother
  exact listExponent_quotientList_eq_of_gap_rotate
    t
    (normalizedProjectiveGaps (genericCutAngles hp i))
    (genericCanonicalCycle hp i hother).gaps
    r hrot

/-- Main cut-invariance theorem for an arbitrary canonical centre-cycle
witness. -/
theorem centreExponent_eq_genericCut
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane}
    (hp : Function.Injective p)
    (i : ProjectionOrdered V)
    (hother : Nonempty (OtherVertex i.toOriginal))
    (C : CentreProjectiveCycle hp i.toOriginal)
    (t : ℝ) :
    centreExponent C t =
      listExponent
        (quotientList t
          (normalizedProjectiveGaps
            (genericCutAngles hp i))) := by
  calc
    centreExponent C t
        =
      centreExponent
        (genericCanonicalCycle hp i hother) t :=
          C.centreExponent_eq
            (genericCanonicalCycle hp i hother) t
    _ =
      listExponent
        (quotientList t
          (normalizedProjectiveGaps
            (genericCutAngles hp i))) :=
      genericCanonical_exponent_eq_genericCut
        hp i hother t

#print axioms genericCanonicalCycle_angles
#print axioms exists_genericCanonical_gap_rotation
#print axioms genericCanonical_exponent_eq_genericCut
#print axioms centreExponent_eq_genericCut

end ProjectionOrdered
end JSP000404Research
