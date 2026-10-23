import JSP000404Research.CyclicTransitionUnitGapSlot
import JSP000404Research.TransitionUnitGapSlot
import JSP000404Research.CentreSignPath
import JSP000404Research.CutNormalizedPhase
import Mathlib.Tactic

/-!
# Dependent bridges for the cyclic wrap unit-gap coordinate

The ordinary q=1 constructor already lives in TransitionUnitGapSlot.  This
file supplies the missing wrap analogue: if the final cyclic quotient of a
displayed centre ray list is one, then the final gap coordinate defines a
CentreUnitGap.

Keeping this dependent-index construction separate makes the later
cut-adjacent-to-canonical-slot proof substantially cleaner.
-/

namespace JSP000404Research

/-- Canonical normalized start coordinate of one cyclic q=1 slot. -/
noncomputable def centreUnitGapStart
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane} {hp : Function.Injective p}
    {i : V}
    (C : CentreProjectiveCycle hp i)
    (t : ℝ)
    (u : CentreUnitGap C t) : ℝ :=
  normalizedRayTheta hp t i
    (C.rays.get (gapToRayIndex C u.1))

noncomputable def globalUnitGapStart
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane} {hp : Function.Injective p}
    (C : ∀ i : V, CentreProjectiveCycle hp i)
    (t : ℝ)
    (u : GlobalUnitGapSlot C t) : ℝ :=
  centreUnitGapStart (C u.1) t u.2

/-- For every ray, its cut-local normalized parameter lifts back to the
canonical normalized parameter after adding either zero or one full period. -/
theorem exists_period_shift_eq_cut_lift
    {V : Type*} {p : V → Plane}
    (hp : Function.Injective p)
    (t c : ℝ)
    (i : V)
    (j : OtherVertex i) :
    ∃ k : ℤ,
      normalizedRayTheta hp t i j + (k : ℝ) * t =
        t * c / Real.pi +
          cutNormalizedRayTheta hp t c i j := by
  by_cases h : rayThetaAt hp i j < c
  · refine ⟨1, ?_⟩
    rw [cutNormalizedRayTheta_eq_normalized_add_period_sub_phase_of_lt hp t j h]
    push_cast
    ring
  · refine ⟨0, ?_⟩
    have hc : c ≤ rayThetaAt hp i j := le_of_not_gt h
    rw [cutNormalizedRayTheta_eq_normalized_sub_phase_of_ge hp t j hc]
    push_cast
    ring


/-- A floor-one cyclic wrap quotient gives the final CentreUnitGap coordinate. -/
theorem exists_centreUnitGap_of_wrap_floor_one
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane} {hp : Function.Injective p}
    {i : V}
    (C : CentreProjectiveCycle hp i)
    (t : ℝ)
    (first : OtherVertex i)
    (rest : List (OtherVertex i))
    (hrays : C.rays = first :: rest)
    (hfloor :
      wrapRayQuotient hp i t first
        (rest.getLastD first) = 1) :
    ∃ u : CentreUnitGap C t,
      u.1.val = rest.length := by
  have hlastGap :
      rest.length < C.gaps.length := by
    rw [C.gaps_length, hrays]
    simp
  let rGap : Fin C.gaps.length :=
    ⟨rest.length, hlastGap⟩
  have hlistLen :
      rest.length < (quotientList t C.gaps).length := by
    rw [quotientList_length]
    exact hlastGap
  let rList : Fin (quotientList t C.gaps).length :=
    ⟨rest.length, hlistLen⟩

  have hdecomp :=
    centreQuotientList_decompose
      C t first rest hrays
  have hlastList :
      (quotientList t C.gaps).get rList = 1 := by
    have hopt :=
      congrArg (fun xs : List ℕ => xs[rest.length]?) hdecomp
    rw [List.getElem?_eq_getElem hlistLen] at hopt
    have hlenQ :
        (consecutiveRayQuotients hp i t first rest).length =
          rest.length :=
      centre_consecutiveRayQuotients_length hp i t first rest
    have htarget :
        (consecutiveRayQuotients hp i t first rest ++
          [wrapRayQuotient hp i t first (rest.getLastD first)])[rest.length]? =
        some 1 := by
      rw [List.getElem?_append_right (by omega)]
      simp [hlenQ, hfloor]
    rw [htarget] at hopt
    change (quotientList t C.gaps)[rest.length] = 1
    exact Option.some_inj.mp hopt

  have hbridge :
      centreQuotient C t rGap =
        (quotientList t C.gaps).get rList := by
    simp [centreQuotient, quotientList, rGap, rList]

  have hunit : centreQuotient C t rGap = 1 := by
    rw [hbridge, hlastList]
  exact ⟨⟨rGap, hunit⟩, rfl⟩

#print axioms exists_centreUnitGap_of_wrap_floor_one

end JSP000404Research
