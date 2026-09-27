import JSP000404Research.TurnUnitSlots
import JSP000404Research.CentreAdjacentTransitionOccurrence
import JSP000404Research.CentreSignPath
import Mathlib.Tactic

/-!
# Dependent constructors for arbitrary whole-unit turn subslots

This generalizes the existing q=1 CentreUnitGap constructors.

For an ordinary adjacent canonical gap or for the final canonical wrap gap,
once its quotient is q and j<q, construct the exact

  CentreTurnUnitSlot = Sigma gapIndex, Fin(quotient)

at offset j.

These constructors contain no phase geometry.  They are the dependent-index
backend used when a saturated cut seam is returned to its canonical cyclic
gap.
-/

namespace JSP000404Research

theorem exists_centreTurnUnitSlot_of_adjacent_floor
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane} {hp : Function.Injective p} {i : V}
    (C : CentreProjectiveCycle hp i)
    (t : ℝ)
    (m q j : ℕ)
    (hm : m + 1 < C.rays.length)
    (hfloor :
      Nat.floor
        (t * ((rayThetaAt hp i
            (C.rays.get ⟨m + 1, hm⟩) -
          rayThetaAt hp i
            (C.rays.get ⟨m, by omega⟩)) / Real.pi)) = q)
    (hj : j < q) :
    ∃ u : CentreTurnUnitSlot C t,
      u.1.val = m ∧
      u.2.val = j ∧
      centreTurnUnitGapQuotient C t u = q := by
  have hmA : m + 1 < C.angles.length := by
    simpa [C.angles_length] using hm
  have hqList :
      (quotientList t C.gaps)[m] = q := by
    rw [centre_adjacent_quotient_getElem_eq C t m hmA]
    simpa [CentreProjectiveCycle.angles] using hfloor
  have hmGap : m < C.gaps.length := by
    rw [C.gaps_length]
    omega
  let rGap : Fin C.gaps.length := ⟨m, hmGap⟩
  let rList : Fin (quotientList t C.gaps).length :=
    ⟨m, by
      rw [quotientList_length]
      exact hmGap⟩
  have hbridge :
      centreQuotient C t rGap =
        (quotientList t C.gaps).get rList := by
    simp [centreQuotient, quotientList, rGap, rList]
  have hlistGet :
      (quotientList t C.gaps).get rList = q := by
    simpa [rList] using hqList
  have hqGap : centreQuotient C t rGap = q := by
    rw [hbridge, hlistGet]
  have hjGap : j < centreQuotient C t rGap := by
    simpa [hqGap] using hj
  let u : CentreTurnUnitSlot C t :=
    ⟨rGap, ⟨j, hjGap⟩⟩
  refine ⟨u, rfl, rfl, ?_⟩
  simpa [centreTurnUnitGapQuotient, u, rGap] using hqGap

theorem exists_centreTurnUnitSlot_of_wrap_floor
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane} {hp : Function.Injective p} {i : V}
    (C : CentreProjectiveCycle hp i)
    (t : ℝ)
    (first : OtherVertex i)
    (rest : List (OtherVertex i))
    (hrays : C.rays = first :: rest)
    (q j : ℕ)
    (hfloor :
      wrapRayQuotient hp i t first
        (rest.getLastD first) = q)
    (hj : j < q) :
    ∃ u : CentreTurnUnitSlot C t,
      u.1.val = rest.length ∧
      u.2.val = j ∧
      centreTurnUnitGapQuotient C t u = q := by
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
      (quotientList t C.gaps).get rList = q := by
    change (quotientList t C.gaps)[rest.length] = q
    rw [hdecomp]
    simp [consecutiveRayQuotients_length, hfloor]
  have hbridge :
      centreQuotient C t rGap =
        (quotientList t C.gaps).get rList := by
    simp [centreQuotient, quotientList, rGap, rList]
  have hqGap : centreQuotient C t rGap = q := by
    rw [hbridge, hlastList]
  have hjGap : j < centreQuotient C t rGap := by
    simpa [hqGap] using hj
  let u : CentreTurnUnitSlot C t :=
    ⟨rGap, ⟨j, hjGap⟩⟩
  refine ⟨u, rfl, rfl, ?_⟩
  simpa [centreTurnUnitGapQuotient, u, rGap] using hqGap

/-- Start of an ordinary constructed slot is the normalized direction at the
left endpoint of the corresponding adjacent canonical gap. -/
theorem centreTurnUnitStart_eq_adjacent_left
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane} {hp : Function.Injective p} {i : V}
    (C : CentreProjectiveCycle hp i)
    (t : ℝ)
    (u : CentreTurnUnitSlot C t)
    (m : ℕ)
    (hm : m < C.rays.length)
    (hu : u.1.val = m) :
    centreTurnUnitStart C t u =
      normalizedRayTheta hp t i
        (C.rays.get ⟨m, hm⟩) + u.2.val := by
  unfold centreTurnUnitStart
  have hidx :
      gapToRayIndex C u.1 = ⟨m, hm⟩ := by
    apply Fin.ext
    simpa using hu
  rw [hidx]

#print axioms exists_centreTurnUnitSlot_of_adjacent_floor
#print axioms exists_centreTurnUnitSlot_of_wrap_floor
#print axioms centreTurnUnitStart_eq_adjacent_left

end JSP000404Research
