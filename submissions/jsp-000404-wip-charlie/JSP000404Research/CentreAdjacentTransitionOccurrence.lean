import JSP000404Research.TransitionQuotientOccurrence
import JSP000404Research.AdjacentProjectiveGapIndex
import JSP000404Research.PinnedCycleRotation
import JSP000404Research.CentreSignPath
import Mathlib.Tactic

/-!
# Indexed transition occurrence in a concrete centre cycle

This file upgrades the previous membership-only adjacent-gap API to a
position-sensitive one.

For an ordinary adjacent pair at ray indices m,m+1:

* the m-th quotient is exactly floor(t * normalized adjacent theta gap);
* the m-th lifted sign step compares exactly those two rays;
* therefore an actual sign change there yields TransitionQuotientOccurs for
  the m-th quotient.

This is the positional bridge needed for exact-witness unit transitions.
-/

namespace JSP000404Research

/-- Pointwise form of quotientList. -/
theorem quotientList_getElem_eq_floor
    (t : ℝ) (gaps : List ℝ)
    (m : ℕ)
    (hm : m < (quotientList t gaps).length) :
    (quotientList t gaps)[m] =
      Nat.floor (t * gaps[m]) := by
  simp [quotientList]

/-- The m-th non-wrap centre quotient is the floor of the m,m+1 adjacent
sorted-angle gap. -/
theorem centre_adjacent_quotient_getElem_eq
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane} {hp : Function.Injective p} {i : V}
    (C : CentreProjectiveCycle hp i)
    (t : ℝ)
    (m : ℕ)
    (hm : m + 1 < C.angles.length) :
    (quotientList t C.gaps)[m] =
      Nat.floor
        (t * ((C.angles[m + 1] - C.angles[m]) / Real.pi)) := by
  obtain ⟨a, xs, hangles⟩ :
      ∃ a xs, C.angles = a :: xs := by
    cases h : C.angles with
    | nil =>
        exact False.elim (C.angles_nonempty h)
    | cons a xs =>
        exact ⟨a, xs, h⟩
  have hmTail : m < xs.length := by
    rw [hangles] at hm
    simpa using hm
  have hmDiff :
      m < (successiveDiffsFrom a xs).length := by
    simpa [successiveDiffsFrom_length] using hmTail
  rw [CentreProjectiveCycle.gaps, hangles]
  simp [quotientList, normalizedProjectiveGaps, projectiveGaps,
    hmDiff,
    successiveDiffsFrom_getElem_eq_adjacent_diff
      a xs m hmTail]

/-- Reading the first m mapped tail signs reaches the sign of ray index m. -/
theorem boolLastFrom_map_take_eq_ray_getElem
    {α : Type*}
    (f : α → Bool)
    (first : α) (rest : List α)
    (m : ℕ)
    (hm : m < (first :: rest).length) :
    boolLastFrom (f first) ((rest.take m).map f) =
      f ((first :: rest)[m]) := by
  induction m generalizing first rest with
  | zero =>
      simp [boolLastFrom]
  | succ m ih =>
      cases rest with
      | nil =>
          simp at hm
      | cons r rs =>
          have hm' : m < (r :: rs).length := by
            simpa using hm
          simpa [boolLastFrom] using
            ih r rs hm'

/-- Ordinary adjacent sign change produces a transition occurrence at the
same indexed quotient. -/
theorem centre_transitionQuotientOccurs_at_adjacent_index
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane}
    (hp : Function.Injective p)
    {i : V}
    (C : CentreProjectiveCycle hp i)
    (t : ℝ)
    (first : OtherVertex i)
    (rest : List (OtherVertex i))
    (hrays : C.rays = first :: rest)
    (m : ℕ)
    (hm : m + 1 < C.rays.length)
    (hchange :
      raySignAt hp i (C.rays[m]) ≠
        raySignAt hp i (C.rays[m + 1])) :
    TransitionQuotientOccurs
      ((quotientList t C.gaps)[m])
      (raySignAt hp i first)
      (liftedCentreSignPath hp i first rest)
      (quotientList t C.gaps) := by
  let sign : OtherVertex i → Bool := raySignAt hp i
  let qs := quotientList t C.gaps
  have hmRest : m < rest.length := by
    rw [hrays] at hm
    simpa using hm
  have hmQs : m < qs.length := by
    dsimp [qs]
    rw [quotientList_length, C.gaps_length]
    exact lt_trans (by omega) hm
  let signPre : List Bool := (rest.take m).map sign
  let signPost : List Bool :=
    (rest.drop (m + 1)).map sign ++
      [!sign first]
  let qPre : List ℕ := qs.take m
  let qPost : List ℕ := qs.drop (m + 1)

  have hrestSplit :
      rest =
        rest.take m ++ rest[m] :: rest.drop (m + 1) := by
    have htake :
        rest.take m ++ [rest[m]] =
          rest.take (m + 1) :=
      List.take_concat_get' rest m hmRest
    have hfull :
        rest.take (m + 1) ++ rest.drop (m + 1) = rest :=
      List.take_append_drop (m + 1) rest
    rw [← hfull, ← htake]
    simp [List.append_assoc]

  have hsignSplit :
      liftedCentreSignPath hp i first rest =
        signPre ++ sign (rest[m]) :: signPost := by
    dsimp [signPre, signPost, sign, liftedCentreSignPath]
    rw [hrestSplit]
    simp [List.map_append, List.append_assoc]

  have hqSplit :
      qs = qPre ++ qs[m] :: qPost := by
    dsimp [qPre, qPost]
    have htake :
        qs.take m ++ [qs[m]] =
          qs.take (m + 1) :=
      List.take_concat_get' qs m hmQs
    have hfull :
        qs.take (m + 1) ++ qs.drop (m + 1) = qs :=
      List.take_append_drop (m + 1) qs
    rw [← hfull, ← htake]
    simp [List.append_assoc]

  have hpreLen :
      signPre.length = qPre.length := by
    dsimp [signPre, qPre]
    simp [List.length_take, hmRest.le, hmQs.le]

  have hprev :
      boolLastFrom (sign first) signPre =
        sign (C.rays[m]) := by
    dsimp [signPre, sign]
    rw [hrays]
    exact boolLastFrom_map_take_eq_ray_getElem
      (raySignAt hp i) first rest m
      (by simp [hmRest])

  have hnext :
      sign (rest[m]) =
        sign (C.rays[m + 1]) := by
    dsimp [sign]
    rw [hrays]
    simp

  rw [hsignSplit, hqSplit]
  apply transitionQuotientOccurs_of_split
      qs[m] (raySignAt hp i first) (sign (rest[m]))
      signPre signPost qPre qPost qs[m]
      hpreLen
  · rw [hprev, hnext]
    exact hchange
  · rfl

theorem consecutiveRayQuotients_length
    {V : Type*} {p : V → Plane}
    (hp : Function.Injective p)
    (i : V) (t : ℝ)
    (first : OtherVertex i)
    (rest : List (OtherVertex i)) :
    (consecutiveRayQuotients hp i t first rest).length =
      rest.length := by
  induction rest generalizing first with
  | nil =>
      rfl
  | cons r rs ih =>
      simp [consecutiveRayQuotients, ih]

/-- A sign change on the cyclic wrap step produces a transition occurrence
at the wrap quotient. -/
theorem centre_transitionQuotientOccurs_at_wrap
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane}
    (hp : Function.Injective p)
    {i : V}
    (C : CentreProjectiveCycle hp i)
    (t : ℝ)
    (first : OtherVertex i)
    (rest : List (OtherVertex i))
    (hrays : C.rays = first :: rest)
    (hchange :
      raySignAt hp i (rest.getLastD first) ≠
        !raySignAt hp i first) :
    TransitionQuotientOccurs
      (wrapRayQuotient hp i t first (rest.getLastD first))
      (raySignAt hp i first)
      (liftedCentreSignPath hp i first rest)
      (quotientList t C.gaps) := by
  let qPre :=
    consecutiveRayQuotients hp i t first rest
  have hq :
      quotientList t C.gaps =
        qPre ++
          [wrapRayQuotient hp i t first
            (rest.getLastD first)] := by
    dsimp [qPre]
    exact centreQuotientList_decompose
      C t first rest hrays
  have hsign :
      liftedCentreSignPath hp i first rest =
        rest.map (raySignAt hp i) ++
          [!raySignAt hp i first] := rfl
  have hlen :
      (rest.map (raySignAt hp i)).length =
        qPre.length := by
    dsimp [qPre]
    rw [List.length_map,
      consecutiveRayQuotients_length hp i t first rest]
  have hlast :
      boolLastFrom
          (raySignAt hp i first)
          (rest.map (raySignAt hp i))
        =
      raySignAt hp i (rest.getLastD first) := by
    rw [boolLastFrom_eq_getLastD, map_getLastD]
  rw [hq, hsign]
  apply transitionQuotientOccurs_of_split
      (wrapRayQuotient hp i t first (rest.getLastD first))
      (raySignAt hp i first)
      (!raySignAt hp i first)
      (rest.map (raySignAt hp i)) []
      qPre []
      (wrapRayQuotient hp i t first (rest.getLastD first))
      hlen
  · rw [hlast]
    exact hchange
  · rfl

#print axioms centre_adjacent_quotient_getElem_eq
#print axioms centre_transitionQuotientOccurs_at_adjacent_index

end JSP000404Research
