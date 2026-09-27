import JSP000404Research.CutCentreTransitionPath
import JSP000404Research.CutLocalBandCycle
import JSP000404Research.SupportTwoTransitionCount
import Mathlib.Tactic

/-!
# Lifted sign path on an arbitrary cut-sorted centre cycle

This is the cut-coordinate analogue of CentreSignPath.

For a CentreCutRayCycle R with rays

  first :: rest,

the cut quotient list splits into ordinary consecutive cut gaps followed by
the final projective wrap gap.  The aligned lifted sign path is

  cutSign(rest) ++ [!cutSign(first)].

Every sign-changing cut step consumes at least one Sendov unit, including the
final wrap step.  Hence the path satisfies ChangesOnlyOnPositive.

In particular, if the canonical positive support is two (equivalently the
cut support is two), the cut lifted path has exactly one sign transition.
-/

namespace JSP000404Research

open Real

def consecutiveCutRayQuotients
    {V : Type*} {p : V → Plane}
    (hp : Function.Injective p)
    (i : V) (t c : ℝ) :
    OtherVertex i → List (OtherVertex i) → List ℕ
  | _, [] => []
  | prev, r :: rs =>
      Nat.floor
        (t * ((cutRayTheta hp c i r -
          cutRayTheta hp c i prev) / Real.pi))
        :: consecutiveCutRayQuotients hp i t c r rs

def cutWrapRayQuotient
    {V : Type*} {p : V → Plane}
    (hp : Function.Injective p)
    (i : V) (t c : ℝ)
    (first last : OtherVertex i) : ℕ :=
  Nat.floor
    (t * ((cutRayTheta hp c i first + Real.pi -
      cutRayTheta hp c i last) / Real.pi))

def cutLiftedCentreSignPath
    {V : Type*} {p : V → Plane}
    (hp : Function.Injective p)
    (c : ℝ) (i : V)
    (first : OtherVertex i)
    (rest : List (OtherVertex i)) : List Bool :=
  rest.map (cutRaySign hp c i) ++
    [!cutRaySign hp c i first]

theorem cutGapQuotients_decompose
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane}
    (hp : Function.Injective p)
    {i : V} {c t : ℝ}
    {C : CentreProjectiveCycle hp i}
    (R : CentreCutRayCycle hp C c)
    (first : OtherVertex i)
    (rest : List (OtherVertex i))
    (hrays : R.rays = first :: rest) :
    R.gapQuotients t =
      consecutiveCutRayQuotients hp i t c first rest ++
        [cutWrapRayQuotient hp i t c first
          (rest.getLastD first)] := by
  unfold CentreCutRayCycle.gapQuotients
  rw [show R.normalizedValues t =
      cutNormalizedRayTheta hp t c i first ::
        rest.map (cutNormalizedRayTheta hp t c i) by
      simp [CentreCutRayCycle.normalizedValues, hrays]]
  simp only [linearCyclicGapQuotients]
  congr 1
  · induction rest generalizing first with
    | nil =>
        rfl
    | cons r rs ih =>
        simp only [successiveDiffsFrom, List.map_cons,
          List.map_map, List.cons_append]
        rw [ih r]
        unfold cutNormalizedRayTheta
        unfold consecutiveCutRayQuotients
        congr 1
        ring
  · unfold cutWrapRayQuotient cutNormalizedRayTheta
    rw [map_getLastD]
    congr 1
    ring

theorem one_le_t_mul_cut_wrap_gap_of_sign_ne
    {V : Type*} {p : V → Plane}
    (hp : Function.Injective p)
    (hcap : AngleCap p lam)
    {lam t c : ℝ}
    (ht : 0 < t)
    (htone : 1 ≤ t)
    (hlam : lam = Real.pi / t)
    (hc0 : 0 ≤ c) (hcpi : c < Real.pi)
    (i : V)
    {first last : OtherVertex i}
    (hfl : first ≠ last)
    (horder :
      cutRayTheta hp c i first ≤
        cutRayTheta hp c i last)
    (hsign :
      cutRaySign hp c i last ≠
        !cutRaySign hp c i first) :
    1 ≤
      t * ((cutRayTheta hp c i first + Real.pi -
        cutRayTheta hp c i last) / Real.pi) := by
  have hfirsti : first.1 ≠ i := first.2
  have hlasti : last.1 ≠ i := last.2
  have hlfVal : last.1 ≠ first.1 :=
    otherVertex_val_ne hfl.symm
  have hcap' :=
    hcap last.1 i first.1 hlasti hlfVal (Ne.symm hfirsti)
  change
    InnerProductGeometry.angle
      (p last.1 - p i) (p first.1 - p i)
      ≤ Real.pi - lam at hcap'

  have hfirstShift :
      p first.1 - p i =
        rayRhoAt hp i first •
          signedRayDirection (!cutRaySign hp c i first)
            (c + cutRayTheta hp c i first + Real.pi) := by
    rw [cutRayRepAt_eq hp c i first]
    rw [signedRayDirection_not_add_pi]
    congr 2
    ring

  rw [cutRayRepAt_eq hp c i last, hfirstShift] at hcap'

  have hphiOrder :
      c + cutRayTheta hp c i last ≤
        c + cutRayTheta hp c i first + Real.pi := by
    have hlastPi :=
      cutRayTheta_lt_pi hp hc0 hcpi i last
    have hfirst0 :=
      cutRayTheta_nonneg hp hc0 hcpi i first
    linarith

  have hspan :
      (c + cutRayTheta hp c i first + Real.pi) -
          (c + cutRayTheta hp c i last)
        ≤ Real.pi := by
    linarith [horder]

  have h :=
    one_le_t_mul_normalized_gap_of_opposite_signs
      (rayRhoAt_pos hp i last)
      (rayRhoAt_pos hp i first)
      ht hlam hphiOrder hspan hsign hcap'
  convert h using 1 <;> ring

theorem floor_cut_wrap_gap_ne_zero_of_sign_ne
    {V : Type*} {p : V → Plane}
    (hp : Function.Injective p)
    (hcap : AngleCap p lam)
    {lam t c : ℝ}
    (ht : 0 < t)
    (hlam : lam = Real.pi / t)
    (hc0 : 0 ≤ c) (hcpi : c < Real.pi)
    (i : V)
    {first last : OtherVertex i}
    (hfl : first ≠ last)
    (horder :
      cutRayTheta hp c i first ≤
        cutRayTheta hp c i last)
    (hsign :
      cutRaySign hp c i last ≠
        !cutRaySign hp c i first) :
    cutWrapRayQuotient hp i t c first last ≠ 0 := by
  have hone :=
    one_le_t_mul_cut_wrap_gap_of_sign_ne
      hp hcap ht hlam hc0 hcpi i hfl horder hsign
  have hfirst0 :=
    cutRayTheta_nonneg hp hc0 hcpi i first
  have hlastPi :=
    cutRayTheta_lt_pi hp hc0 hcpi i last
  have hnonneg :
      0 ≤ t * ((cutRayTheta hp c i first + Real.pi -
        cutRayTheta hp c i last) / Real.pi) := by
    positivity
  unfold cutWrapRayQuotient
  have hfloor :
      1 ≤ Nat.floor
        (t * ((cutRayTheta hp c i first + Real.pi -
          cutRayTheta hp c i last) / Real.pi)) := by
    apply Nat.le_floor hnonneg
    exact_mod_cast hone
  omega

theorem consecutiveCut_changesOnlyOnPositive
    {V : Type*} {p : V → Plane}
    (hp : Function.Injective p)
    (hcap : AngleCap p lam)
    {lam t c : ℝ}
    (ht : 0 < t)
    (hlam : lam = Real.pi / t)
    (hc0 : 0 ≤ c) (hcpi : c < Real.pi)
    (i : V)
    (prev : OtherVertex i)
    (rs : List (OtherVertex i))
    (hnodup : (prev :: rs).Nodup)
    (hsorted :
      (prev :: rs).Pairwise
        (fun a b =>
          cutRayTheta hp c i a ≤ cutRayTheta hp c i b)) :
    ChangesOnlyOnPositive
      (cutRaySign hp c i prev)
      (rs.map (cutRaySign hp c i))
      (consecutiveCutRayQuotients hp i t c prev rs) := by
  induction rs generalizing prev with
  | nil =>
      simp [ChangesOnlyOnPositive, consecutiveCutRayQuotients]
  | cons r rs ih =>
      have hnod := List.nodup_cons.mp hnodup
      have hpair := List.pairwise_cons.mp hsorted
      have hprevR : prev ≠ r := by
        intro h
        subst r
        exact hnod.1 (by simp)
      have horder :
          cutRayTheta hp c i prev ≤ cutRayTheta hp c i r :=
        hpair.1 r (by simp)
      constructor
      · intro hsign
        have hone :=
          one_le_t_mul_cutRay_gap_of_sign_ne
            hp hcap ht hlam hc0 hcpi i
            hprevR horder hsign
        have hgap0 :
            0 ≤
              t * ((cutRayTheta hp c i r -
                cutRayTheta hp c i prev) / Real.pi) := by
          positivity
        have hfloor :
            1 ≤ Nat.floor
              (t * ((cutRayTheta hp c i r -
                cutRayTheta hp c i prev) / Real.pi)) := by
          apply Nat.le_floor hgap0
          exact_mod_cast hone
        omega
      · exact ih r hnod.2 hpair.2

theorem cutCentre_changesOnlyOnPositive
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane}
    (hp : Function.Injective p)
    (hcap : AngleCap p lam)
    {lam t c : ℝ}
    (ht : 0 < t)
    (htone : 1 ≤ t)
    (hlam : lam = Real.pi / t)
    (hc0 : 0 ≤ c) (hcpi : c < Real.pi)
    {i : V}
    {C : CentreProjectiveCycle hp i}
    (R : CentreCutRayCycle hp C c)
    (first : OtherVertex i)
    (rest : List (OtherVertex i))
    (hrays : R.rays = first :: rest) :
    ChangesOnlyOnPositive
      (cutRaySign hp c i first)
      (cutLiftedCentreSignPath hp c i first rest)
      (R.gapQuotients t) := by
  have hnod :
      (first :: rest).Nodup := by
    simpa [hrays] using R.nodup
  have hsorted :
      (first :: rest).Pairwise
        (fun a b =>
          cutRayTheta hp c i a ≤ cutRayTheta hp c i b) := by
    simpa [hrays] using R.cutTheta_sorted

  have hord :=
    consecutiveCut_changesOnlyOnPositive
      hp hcap ht hlam hc0 hcpi
      i first rest hnod hsorted

  rw [cutGapQuotients_decompose hp R first rest hrays]
  unfold cutLiftedCentreSignPath
  apply changesOnlyOnPositive_append_singleton
    (cutRaySign hp c i first)
    (!cutRaySign hp c i first)
    (rest.map (cutRaySign hp c i))
    (consecutiveCutRayQuotients hp i t c first rest)
    (cutWrapRayQuotient hp i t c first (rest.getLastD first))
    hord

  intro hsign
  have hlastSign :
      boolLastFrom
          (cutRaySign hp c i first)
          (rest.map (cutRaySign hp c i))
        =
      cutRaySign hp c i (rest.getLastD first) := by
    rw [boolLastFrom_eq_getLastD, map_getLastD]
  rw [hlastSign] at hsign
  by_cases hrest : rest = []
  · subst rest
    unfold cutWrapRayQuotient
    simp only [List.getLastD_nil]
    have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
    have harg :
        t * ((cutRayTheta hp c i first + Real.pi -
          cutRayTheta hp c i first) / Real.pi) = t := by
      field_simp [hpi]
    rw [harg]
    have ht0 : 0 ≤ t := ht.le
    have hfloor : 1 ≤ Nat.floor t := by
      apply Nat.le_floor ht0
      exact_mod_cast htone
    omega
  · let last := rest.getLastD first
    have hlastMem : last ∈ rest := by
      dsimp [last]
      exact List.getLastD_mem hrest
    have hfl : first ≠ last := by
      intro h
      subst last
      exact (List.nodup_cons.mp hnod).1 hlastMem
    have horder :
        cutRayTheta hp c i first ≤
          cutRayTheta hp c i last :=
      (List.pairwise_cons.mp hsorted).1 last hlastMem
    exact floor_cut_wrap_gap_ne_zero_of_sign_ne
      hp hcap ht hlam hc0 hcpi i
      hfl horder hsign

theorem cutLiftedCentreSignPath_last_not
    {V : Type*} {p : V → Plane}
    (hp : Function.Injective p)
    (c : ℝ) (i : V)
    (first : OtherVertex i)
    (rest : List (OtherVertex i)) :
    boolLastFrom
      (cutRaySign hp c i first)
      (cutLiftedCentreSignPath hp c i first rest)
      =
    !cutRaySign hp c i first := by
  unfold cutLiftedCentreSignPath
  exact boolLastFrom_append_singleton _ _ _

theorem cutCentre_support_two_transitionCount_eq_one
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane}
    (hp : Function.Injective p)
    (hcap : AngleCap p lam)
    {lam t c : ℝ}
    (ht : 0 < t)
    (hlam : lam = Real.pi / t)
    (hc0 : 0 ≤ c) (hcpi : c < Real.pi)
    {i : V}
    {C : CentreProjectiveCycle hp i}
    (R : CentreCutRayCycle hp C c)
    (first : OtherVertex i)
    (rest : List (OtherVertex i))
    (hrays : R.rays = first :: rest)
    (hsupport :
      positiveSupport (centreQuotient C t) = 2) :
    boolTransitionCountFrom
        (cutRaySign hp c i first)
        (cutLiftedCentreSignPath hp c i first rest)
      = 1 := by
  have hchanges :=
    cutCentre_changesOnlyOnPositive
      hp hcap ht htone hlam hc0 hcpi R first rest hrays
  have hle :=
    transitionCount_le_positiveCount_of_changesOnlyOnPositive
      (cutRaySign hp c i first)
      (cutLiftedCentreSignPath hp c i first rest)
      (R.gapQuotients t) hchanges
  have hsupportCut :=
    R.gapQuotients_positiveCount_eq_canonical hp ht
  rw [hsupport] at hsupportCut
  rw [hsupportCut] at hle
  exact boolTransitionCountFrom_eq_one_of_last_not_of_le_two
    (cutRaySign hp c i first)
    (cutLiftedCentreSignPath hp c i first rest)
    (cutLiftedCentreSignPath_last_not hp c i first rest)
    hle

#print axioms cutGapQuotients_decompose
#print axioms floor_cut_wrap_gap_ne_zero_of_sign_ne
#print axioms cutCentre_changesOnlyOnPositive
#print axioms cutCentre_support_two_transitionCount_eq_one

end JSP000404Research
