import JSP000404Research.CanonicalSignGap
import JSP000404Research.SignPathAppend
import JSP000404Research.CentreExponent
import Mathlib.Tactic

/-!
# The actual centre sign path changes only on positive Sendov quotients

Let the canonical projective rays at one centre be sorted as

  r0, r1, ..., r_{m-1}

with parameters in [0,pi).  The m cyclic projective gaps are the m-1
successive differences followed by the wrap gap.

The lifted sign path aligned with those m gaps starts at sign(r0), then reads

  sign(r1), ..., sign(r_{m-1}), !sign(r0).

The final flipped sign is the representation of the first ray at theta0+pi.

Under the global angle cap with lambda=pi/t, every sign-changing step consumes
at least one normalized cap unit.  Hence every sign change is carried by a
positive Sendov quotient.  The theorem in this file supplies the previously
abstract ChangesOnlyOnPositive hypothesis for the concrete centre cycle.
-/

namespace JSP000404Research

open Real

/-- Mapping commutes with getLastD. -/
theorem map_getLastD
    {α β : Type*} (f : α → β) (d : α) (xs : List α) :
    (xs.map f).getLastD (f d) = f (xs.getLastD d) := by
  cases xs with
  | nil => rfl
  | cons x xs =>
      simp

/-- boolLastFrom is just getLastD with the initial sign as default. -/
theorem boolLastFrom_eq_getLastD
    (a : Bool) (xs : List Bool) :
    boolLastFrom a xs = xs.getLastD a := by
  induction xs generalizing a with
  | nil => rfl
  | cons b bs ih =>
      simp only [boolLastFrom]
      rw [ih]
      simp

/-- Quotients of the ordinary non-wrap gaps along a ray list. -/
def consecutiveRayQuotients
    {V : Type*} {p : V → Plane}
    (hp : Function.Injective p)
    (i : V) (t : ℝ) :
    OtherVertex i → List (OtherVertex i) → List ℕ
  | _, [] => []
  | prev, r :: rs =>
      Nat.floor
          (t * ((rayThetaAt hp i r - rayThetaAt hp i prev) / Real.pi))
        :: consecutiveRayQuotients hp i t r rs

/-- The ordinary consecutive quotients are exactly quotientList applied to the
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

/-- Every sign change across an ordinary sorted adjacent gap has positive
quotient. -/
theorem consecutive_changesOnlyOnPositive
    {V : Type*} {p : V → Plane}
    (hp : Function.Injective p)
    (hcap : AngleCap p lam)
    {lam t : ℝ}
    (ht : 0 < t)
    (hlam : lam = Real.pi / t)
    (i : V)
    (prev : OtherVertex i) (rs : List (OtherVertex i))
    (hnodup : (prev :: rs).Nodup)
    (hsorted :
      (prev :: rs).Pairwise
        (fun a b =>
          rayThetaAt hp i a ≤ rayThetaAt hp i b)) :
    ChangesOnlyOnPositive
      (raySignAt hp i prev)
      (rs.map (raySignAt hp i))
      (consecutiveRayQuotients hp i t prev rs) := by
  induction rs generalizing prev with
  | nil =>
      simp [ChangesOnlyOnPositive, consecutiveRayQuotients]
  | cons r rs ih =>
      have hnod := List.nodup_cons.mp hnodup
      have hpair := List.pairwise_cons.mp hsorted
      have hprevR : prev ≠ r := by
        intro h
        subst r
        exact hnod.1 (by simp)
      have horder :
          rayThetaAt hp i prev ≤ rayThetaAt hp i r :=
        hpair.1 r (by simp)
      constructor
      · intro hsign
        exact floor_t_mul_gap_ne_zero_of_canonical_sign_ne
          hp hcap ht hlam i hprevR horder hsign
      · exact ih r hnod.2 hpair.2

/-- The normalized wrap quotient from the last ray back to the lifted first
ray. -/
def wrapRayQuotient
    {V : Type*} {p : V → Plane}
    (hp : Function.Injective p)
    (i : V) (t : ℝ)
    (first last : OtherVertex i) : ℕ :=
  Nat.floor
    (t * ((rayThetaAt hp i first + Real.pi -
      rayThetaAt hp i last) / Real.pi))

/-- Decomposition of the concrete quotient list into ordinary consecutive
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
  simp only [List.map_cons, normalizedProjectiveGaps, projectiveGaps,
    List.map_append, List.map_singleton, quotientList, List.map_map]
  rw [← consecutiveRayQuotients_eq_quotientList]
  congr 2
  simp [wrapRayQuotient, map_getLastD]

/-- The concrete lifted cyclic sign path. -/
def liftedCentreSignPath
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane} (hp : Function.Injective p)
    (i : V)
    (first : OtherVertex i)
    (rest : List (OtherVertex i)) : List Bool :=
  rest.map (raySignAt hp i) ++ [!raySignAt hp i first]

/-- The actual cyclic sign path changes only on positive concrete centre
quotients. -/
theorem centre_changesOnlyOnPositive
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane}
    (hp : Function.Injective p)
    (hcap : AngleCap p lam)
    {lam t : ℝ}
    (ht : 0 < t)
    (htone : 1 ≤ t)
    (hlam : lam = Real.pi / t)
    (i : V)
    (C : CentreProjectiveCycle hp i)
    (first : OtherVertex i)
    (rest : List (OtherVertex i))
    (hrays : C.rays = first :: rest) :
    ChangesOnlyOnPositive
      (raySignAt hp i first)
      (liftedCentreSignPath hp i first rest)
      (quotientList t C.gaps) := by
  have hnodup :
      (first :: rest).Nodup := by
    simpa [hrays] using C.nodup
  have hsorted :
      (first :: rest).Pairwise
        (fun a b =>
          rayThetaAt hp i a ≤ rayThetaAt hp i b) := by
    simpa [hrays] using C.theta_sorted
  have hordinary :=
    consecutive_changesOnlyOnPositive
      hp hcap ht hlam i first rest hnodup hsorted
  rw [centreQuotientList_decompose C t first rest hrays]
  unfold liftedCentreSignPath
  apply changesOnlyOnPositive_append_singleton
    (raySignAt hp i first)
    (!raySignAt hp i first)
    (rest.map (raySignAt hp i))
    (consecutiveRayQuotients hp i t first rest)
    (wrapRayQuotient hp i t first (rest.getLastD first))
    hordinary
  intro hsign
  have hlastSign :
      boolLastFrom
          (raySignAt hp i first)
          (rest.map (raySignAt hp i))
        =
      raySignAt hp i (rest.getLastD first) := by
    rw [boolLastFrom_eq_getLastD, map_getLastD]
  rw [hlastSign] at hsign
  by_cases hrest : rest = []
  · subst rest
    have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
    have harg :
        t * ((rayThetaAt hp i first + Real.pi -
          rayThetaAt hp i first) / Real.pi) = t := by
      field_simp [hpi]
    unfold wrapRayQuotient
    simp only [List.getLastD_nil]
    rw [harg]
    have ht0 : 0 ≤ t := ht.le
    have hfloor : 1 ≤ Nat.floor t := by
      apply Nat.le_floor ht0
      exact_mod_cast htone
    omega
  · let last : OtherVertex i := rest.getLastD first
    have hlastMem : last ∈ rest := by
      dsimp [last]
      exact List.getLastD_mem hrest
    have hfirstLast : first ≠ last := by
      intro h
      subst last
      exact (List.nodup_cons.mp hnodup).1 hlastMem
    have hpair := List.pairwise_cons.mp hsorted
    have horder :
        rayThetaAt hp i first ≤ rayThetaAt hp i last :=
      hpair.1 last hlastMem
    exact floor_t_mul_wrap_gap_ne_zero_of_canonical_sign_ne
      hp hcap ht hlam i hfirstLast horder hsign

/-- The lifted centre path is antiperiodic by construction. -/
theorem liftedCentreSignPath_last_not
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane}
    (hp : Function.Injective p)
    (i : V)
    (first : OtherVertex i)
    (rest : List (OtherVertex i)) :
    boolLastFrom
        (raySignAt hp i first)
        (liftedCentreSignPath hp i first rest)
      =
    !raySignAt hp i first := by
  unfold liftedCentreSignPath
  exact boolLastFrom_append_singleton _ _ _

#print axioms consecutive_changesOnlyOnPositive
#print axioms centreQuotientList_decompose
#print axioms centre_changesOnlyOnPositive
#print axioms liftedCentreSignPath_last_not

end JSP000404Research
