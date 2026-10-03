import JSP000404Research.CentreQuotientData
import Mathlib.Tactic

/-!
# Quotient data along the canonical centre ray cycle

This lightweight module contains only the quotient-list data needed to align
actual cyclic ray angles with the canonical normalized projective gaps.

It is intentionally separated from the heavier Boolean sign-path machinery.
-/

namespace JSP000404Research

/-- Mapping commutes with getLastD. -/
theorem map_getLastD
    {α β : Type*} (f : α → β) (d : α) (xs : List α) :
    (xs.map f).getLastD (f d) = f (xs.getLastD d) := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
      cases xs with
      | nil => simp
      | cons y ys =>
          exact ih

/-- Quotients of the ordinary non-wrap gaps along a ray list. -/
noncomputable def consecutiveRayQuotients
    {V : Type*} {p : V → Plane}
    (hp : Function.Injective p)
    (i : V) (t : ℝ) :
    OtherVertex i → List (OtherVertex i) → List ℕ
  | _, [] => []
  | prev, r :: rs =>
      Nat.floor
          (t * ((rayThetaAt hp i r - rayThetaAt hp i prev) / Real.pi))
        :: consecutiveRayQuotients hp i t r rs

/-- Ordinary consecutive quotients are exactly the quotient list of the
normalized successive-difference gaps. -/
theorem consecutiveRayQuotients_eq_quotientList
    {V : Type*} {p : V → Plane}
    (hp : Function.Injective p)
    (i : V) (t : ℝ)
    (prev : OtherVertex i) (rs : List (OtherVertex i)) :
    consecutiveRayQuotients hp i t prev rs =
      quotientList t
        ((successiveDiffsFrom
            (rayThetaAt hp i prev)
            (rs.map (rayThetaAt hp i))).map
          (fun d => d / Real.pi)) := by
  induction rs generalizing prev with
  | nil =>
      simp [consecutiveRayQuotients, successiveDiffsFrom, quotientList]
  | cons r rs ih =>
      simp [consecutiveRayQuotients, successiveDiffsFrom,
        quotientList, ih]

/-- The normalized wrap quotient from the last ray back to the lifted first
ray. -/
noncomputable def wrapRayQuotient
    {V : Type*} {p : V → Plane}
    (hp : Function.Injective p)
    (i : V) (t : ℝ)
    (first last : OtherVertex i) : ℕ :=
  Nat.floor
    (t * ((rayThetaAt hp i first + Real.pi -
      rayThetaAt hp i last) / Real.pi))

/-- Decompose the concrete centre quotient list into ordinary consecutive
quotients and the final wrap quotient. -/
theorem centreQuotientList_decompose
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane} {hp : Function.Injective p} {i : V}
    (C : CentreProjectiveCycle hp i)
    (t : ℝ)
    (first : OtherVertex i) (rest : List (OtherVertex i))
    (hrays : C.rays = first :: rest) :
    quotientList t C.gaps =
      consecutiveRayQuotients hp i t first rest ++
        [wrapRayQuotient hp i t first (rest.getLastD first)] := by
  rw [CentreProjectiveCycle.gaps, CentreProjectiveCycle.angles, hrays]
  change
    quotientList t
        ((successiveDiffsFrom
            (rayThetaAt hp i first)
            (rest.map (rayThetaAt hp i))).map
          (fun d => d / Real.pi))
      ++
      [Nat.floor
        (t * ((rayThetaAt hp i first + Real.pi -
          (rest.map (rayThetaAt hp i)).getLastD
            (rayThetaAt hp i first)) / Real.pi))]
      =
    consecutiveRayQuotients hp i t first rest ++
      [wrapRayQuotient hp i t first (rest.getLastD first)]
  rw [← consecutiveRayQuotients_eq_quotientList]
  congr 1
  simp [wrapRayQuotient, map_getLastD]

#print axioms consecutiveRayQuotients_eq_quotientList
#print axioms centreQuotientList_decompose

end JSP000404Research
