import JSP000404Research.CanonicalSignGap
import JSP000404Research.SignPathAppend
import JSP000404Research.CentreExponent
import JSP000404Research.CentreQuotientRayData
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

/-- boolLastFrom is just getLastD with the initial sign as default. -/
theorem boolLastFrom_eq_getLastD
    (a : Bool) (xs : List Bool) :
    boolLastFrom a xs = xs.getLastD a := by
  induction xs generalizing a with
  | nil => rfl
  | cons b bs ih =>
      cases bs with
      | nil => simp [boolLastFrom]
      | cons c cs =>
          simp only [boolLastFrom]
          simpa [boolLastFrom] using ih a

/-- The concrete lifted cyclic sign path. -/
noncomputable def liftedCentreSignPath
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
    {lam t : ℝ}
    (hp : Function.Injective p)
    (hcap : AngleCap p lam)
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
      ring
    unfold wrapRayQuotient
    simp only [List.getLastD_nil]
    rw [harg]
    have hfloor : 1 ≤ Nat.floor t := by
      exact Nat.le_floor (by exact_mod_cast htone)
    omega
  · let last : OtherVertex i := rest.getLastD first
    have hlastMem : last ∈ rest := by
      dsimp [last]
      exact getLastD_mem_of_ne_nil first rest hrest
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
