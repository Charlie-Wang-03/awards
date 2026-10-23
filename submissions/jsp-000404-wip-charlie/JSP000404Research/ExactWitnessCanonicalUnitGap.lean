import JSP000404Research.ExactWitnessUnitGapMass
import JSP000404Research.CentreExponent
import JSP000404Research.AdjacentProjectiveGapIndex
import JSP000404Research.TurnUnitGapBridge
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

/-!
The exact-witness theorem below uses the already kernel-checked dependent
turn-unit-gap bridge. This avoids duplicating the subtle Fin/getElem
transport proofs for the ordinary and wrap positions.
-/

/-- Every exact maximum-angle witness has one canonical cyclic gap whose
natural quotient and exact scaled width are both exactly one. -/
theorem exists_exactWitness_canonical_unit_gap
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane}
    (hp : Function.Injective p)
    {lam t delta : ℝ} {n : ℕ}
    (hcap : AngleCap p lam)
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
      hp hcap hn hdelta0 ht hlam W C with hord | hwrap
  · obtain ⟨m, hm, hscaled, _hsign⟩ := hord
    have hfloor :
        Nat.floor
          (t * ((rayThetaAt hp W.b
              (C.rays.get ⟨m + 1, hm⟩) -
            rayThetaAt hp W.b
              (C.rays.get ⟨m, by omega⟩)) / Real.pi)) = 1 := by
      rw [hscaled]
      norm_num
    obtain ⟨u, huIndex, _huOffset, huQuotient⟩ :=
      exists_centreTurnUnitSlot_of_adjacent_floor
        C t m 1 0 hm hfloor (by decide)
    let e : Fin C.gaps.length := u.1
    have hscaled' : t * C.gaps.get e = 1 := by
      have hgap :=
        centreTurnUnitGapScaledLength_eq_adjacent
          C t u m hm huIndex
      change t * C.gaps.get u.1 = _ at hgap
      rw [hgap]
      exact hscaled
    refine ⟨e, ?_, hscaled'⟩
    simpa [e, centreTurnUnitGapQuotient] using huQuotient
  · obtain ⟨first, rest, hrays, hscaled, _hsign⟩ := hwrap
    have hfloor :
        wrapRayQuotient hp W.b t first (rest.getLastD first) = 1 := by
      unfold wrapRayQuotient
      rw [hscaled]
      norm_num
    obtain ⟨u, huIndex, _huOffset, huQuotient⟩ :=
      exists_centreTurnUnitSlot_of_wrap_floor
        C t first rest hrays 1 0 hfloor (by decide)
    let e : Fin C.gaps.length := u.1
    have hscaled' : t * C.gaps.get e = 1 := by
      have hgap :=
        centreTurnUnitGapScaledLength_eq_wrap
          C t u first rest hrays huIndex
      change t * C.gaps.get u.1 = _ at hgap
      rw [hgap]
      exact hscaled
    refine ⟨e, ?_, hscaled'⟩
    simpa [e, centreTurnUnitGapQuotient] using huQuotient

#print axioms exists_exactWitness_canonical_unit_gap

end JSP000404Research
