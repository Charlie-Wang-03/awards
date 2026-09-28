import JSP000404Research.ExactWitnessUnitGapMass
import JSP000404Research.CentreExponent
import JSP000404Research.AdjacentProjectiveGapIndex
import Mathlib.Tactic

/-!
# Canonical exact unit gap at an exact maximum-angle witness

ExactWitnessUnitGapMass keeps the exact physical statement that one ordinary
or wrap transition gap at the witness centre has Sendov-scaled width exactly
one.  This file ties that geometric gap to a single canonical dependent index

  e : Fin C.gaps.length.

At that same index we retain both

  centreQuotient C t e = 1
  t * C.gaps.get e = 1.

This is the index-level bridge needed to rotate the exact witness gap together
with the sharp-pinned support-three quotient shape.
-/

namespace JSP000404Research

open Real

/-- The m-th ordinary canonical projective gap is the normalized difference of
the m-th and (m+1)-st sorted ray parameters. -/
theorem centre_gap_get_adjacent_eq
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane} {hp : Function.Injective p} {i : V}
    (C : CentreProjectiveCycle hp i)
    (m : ℕ)
    (hm : m + 1 < C.rays.length) :
    C.gaps.get
        ⟨m, by
          rw [C.gaps_length]
          omega⟩
      =
    (rayThetaAt hp i
          (C.rays.get ⟨m + 1, hm⟩) -
        rayThetaAt hp i
          (C.rays.get ⟨m, by omega⟩)) /
      Real.pi := by
  have hmA : m + 1 < C.angles.length := by
    rw [C.angles_length]
    exact hm
  obtain ⟨a, xs, hangles⟩ :
      ∃ a xs, C.angles = a :: xs := by
    cases h : C.angles with
    | nil => exact False.elim (C.angles_nonempty h)
    | cons a xs => exact ⟨a, xs, h⟩
  have hmTail : m < xs.length := by
    rw [hangles] at hmA
    simpa using hmA
  have hmDiff :
      m < (successiveDiffsFrom a xs).length := by
    simpa [successiveDiffsFrom_length] using hmTail
  rw [CentreProjectiveCycle.gaps, hangles]
  simp only [normalizedProjectiveGaps, projectiveGaps,
    List.map_append, List.map_singleton]
  simp [hmDiff,
    successiveDiffsFrom_getElem_eq_adjacent_diff
      a xs m hmTail,
    CentreProjectiveCycle.angles, hangles]

/-- The final canonical projective gap is the normalized wrap difference. -/
theorem centre_gap_get_wrap_eq
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane} {hp : Function.Injective p} {i : V}
    (C : CentreProjectiveCycle hp i)
    (first : OtherVertex i)
    (rest : List (OtherVertex i))
    (hrays : C.rays = first :: rest) :
    C.gaps.get
        ⟨rest.length, by
          rw [C.gaps_length, hrays]
          simp⟩
      =
    (rayThetaAt hp i first + Real.pi -
        rayThetaAt hp i (rest.getLastD first)) /
      Real.pi := by
  rw [CentreProjectiveCycle.gaps,
      CentreProjectiveCycle.angles, hrays]
  simp [normalizedProjectiveGaps, projectiveGaps]

/-- Every exact maximum-angle witness has one canonical cyclic gap whose
natural quotient and exact scaled width are both exactly one. -/
theorem exists_exactWitness_canonical_unit_gap
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane}
    (hp : Function.Injective p)
    (hcap : AngleCap p lam)
    {lam t delta : ℝ} {n : ℕ}
    (hn : 3 ≤ n)
    (hdelta0 : 0 ≤ delta)
    (ht : t = (n : ℝ) + delta)
    (hlam : lam = Real.pi / t)
    (W : ExactAngleWitness p lam)
    (C : CentreProjectiveCycle hp W.b) :
    ∃ e : Fin C.gaps.length,
      centreQuotient C t e = 1 ∧
      t * C.gaps.get e = 1 := by
  rcases exactWitness_unit_transition_gap_position
      hp hcap hn hdelta0 ht hlam W C
    with hord | hwrap
  · obtain ⟨m, hm, hscaled, _hsign⟩ := hord
    let e : Fin C.gaps.length :=
      ⟨m, by
        rw [C.gaps_length]
        omega⟩
    have hgap :
        C.gaps.get e =
          (rayThetaAt hp W.b
              (C.rays.get ⟨m + 1, hm⟩) -
            rayThetaAt hp W.b
              (C.rays.get ⟨m, by omega⟩)) /
            Real.pi := by
      simpa [e] using centre_gap_get_adjacent_eq C m hm
    have hscaled' : t * C.gaps.get e = 1 := by
      rw [hgap]
      exact hscaled
    refine ⟨e, ?_, hscaled'⟩
    unfold centreQuotient
    rw [hscaled']
    norm_num
  · obtain ⟨first, rest, hrays, hscaled, _hsign⟩ := hwrap
    let e : Fin C.gaps.length :=
      ⟨rest.length, by
        rw [C.gaps_length, hrays]
        simp⟩
    have hgap :
        C.gaps.get e =
          (rayThetaAt hp W.b first + Real.pi -
            rayThetaAt hp W.b (rest.getLastD first)) /
            Real.pi := by
      simpa [e] using centre_gap_get_wrap_eq C first rest hrays
    have hscaled' : t * C.gaps.get e = 1 := by
      rw [hgap]
      exact hscaled
    refine ⟨e, ?_, hscaled'⟩
    unfold centreQuotient
    rw [hscaled']
    norm_num

#print axioms centre_gap_get_adjacent_eq
#print axioms centre_gap_get_wrap_eq
#print axioms exists_exactWitness_canonical_unit_gap

end JSP000404Research
