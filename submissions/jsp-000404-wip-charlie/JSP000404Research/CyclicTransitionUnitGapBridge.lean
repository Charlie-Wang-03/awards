import JSP000404Research.CyclicTransitionUnitGapSlot
import JSP000404Research.TransitionUnitGapSlot
import JSP000404Research.CentreSignPath
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
    change (quotientList t C.gaps)[rest.length] = 1
    rw [hdecomp]
    simp [consecutiveRayQuotients_length, hfloor]

  have hbridge :
      centreQuotient C t rGap =
        (quotientList t C.gaps).get rList := by
    simp [centreQuotient, quotientList, rGap, rList]

  have hunit : centreQuotient C t rGap = 1 := by
    rw [hbridge, hlastList]
  exact ⟨⟨rGap, hunit⟩, rfl⟩

#print axioms exists_centreUnitGap_of_wrap_floor_one

end JSP000404Research
