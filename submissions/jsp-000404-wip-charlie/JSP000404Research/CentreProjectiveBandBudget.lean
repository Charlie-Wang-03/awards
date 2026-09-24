
import JSP000404Research.ProjectiveGapScaling
import JSP000404Research.ProjectiveBandOccupancy
import JSP000404Research.CentreExponent
import Mathlib.Tactic

/-!
# Centre exponent is paid by missing canonical projective bands

This file closes the local interface between the concrete Sendov centre
exponent and the direct canonical projective-band BinaryEdgePartition.

For one centre C:

* scale its sorted canonical projective angles by t/pi;
* their natural floor indices are exactly the occupied projective unit bands;
* ProjectiveGapScaling identifies the concrete Sendov quotient list with the
  floors of the cyclic gaps of these scaled coordinates;
* ScaledCyclicBandBudget pays every quotient excess by an empty unit band.

Therefore, for t=n+delta with 0<=delta<1,

  centreExponent(C,t)
    <= (n+1) - card(occupiedProjectiveBands).

Since ProjectiveBandOccupancy identifies occupiedProjectiveBands with the
active colours of the global direct BinaryEdgePartition, we obtain the exact
one-layer active-colour budget

  active(i).card <= (n+1) - centreExponent(C_i,t).

This is the first direct formal bridge from the genuine centre projective gap
exponent to a global Hansel/BinaryEdgePartition local palette.
-/

namespace JSP000404Research

open Real

noncomputable def rayProjectiveBand
    {V : Type*} {p : V → Plane}
    (hp : Function.Injective p)
    {t : ℝ} (ht : 0 < t)
    (n : ℕ)
    (htop : t < (n + 1 : ℕ))
    (i : V) (j : OtherVertex i) :
    Fin (n + 1) :=
  projectiveBandColor hp ht n htop i j.1

noncomputable def centreProjectiveBandList
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane} {hp : Function.Injective p} {i : V}
    (C : CentreProjectiveCycle hp i)
    {t : ℝ} (ht : 0 < t)
    (n : ℕ)
    (htop : t < (n + 1 : ℕ)) :
    List (Fin (n + 1)) :=
  C.rays.map (rayProjectiveBand hp ht n htop i)

def scaledCentreAngles
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane} {hp : Function.Injective p} {i : V}
    (C : CentreProjectiveCycle hp i)
    (t : ℝ) : List ℝ :=
  C.angles.map (scaleProjectiveAngle t)

def centreFloorBandList
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane} {hp : Function.Injective p} {i : V}
    (C : CentreProjectiveCycle hp i)
    (t : ℝ) : List ℕ :=
  floorBandList (scaledCentreAngles C t)

/-- Every ray's finite projective band contains that ray. -/
theorem rayProjectiveBand_mem
    {V : Type*} {p : V → Plane}
    (hp : Function.Injective p)
    {t : ℝ} (ht : 0 < t)
    (n : ℕ)
    (htop : t < (n + 1 : ℕ))
    (i : V) (j : OtherVertex i) :
    RayInProjectiveBand hp t i j
      (rayProjectiveBand hp ht n htop i j) := by
  exact projectiveBandColor_mem_lower
    hp ht n htop j.2.symm

/-- The occupied-band finset is exactly the finset of ray-band values in the
canonical centre cycle. -/
theorem occupiedProjectiveBands_eq_centreBandList_toFinset
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane} (hp : Function.Injective p)
    {t : ℝ} (ht : 0 < t)
    (n : ℕ)
    (htop : t < (n + 1 : ℕ))
    (i : V)
    (C : CentreProjectiveCycle hp i) :
    occupiedProjectiveBands hp t n i =
      (centreProjectiveBandList C ht n htop).toFinset := by
  classical
  ext c
  constructor
  · intro hc
    obtain ⟨j, hjBand⟩ :=
      (mem_occupiedProjectiveBands hp t n i c).1 hc
    have hjRay : j ∈ C.rays :=
      C.mem_rays_iff j
    have hcol :
        rayProjectiveBand hp ht n htop i j = c := by
      exact projectiveBandColor_eq_of_lower_ray_mem
        hp ht n htop j.2.symm c hjBand
    simp only [centreProjectiveBandList, List.mem_toFinset,
      List.mem_map]
    exact ⟨j, hjRay, hcol⟩
  · intro hc
    have hcList :
        c ∈ centreProjectiveBandList C ht n htop := by
      simpa using hc
    obtain ⟨j, hjRay, hjeq⟩ := by
      simpa [centreProjectiveBandList] using hcList
    apply (mem_occupiedProjectiveBands hp t n i c).2
    refine ⟨j, ?_⟩
    rw [← hjeq]
    exact rayProjectiveBand_mem
      hp ht n htop i j

/-- The natural floor-band list of the scaled centre angles is the value-list
of the finite ray bands. -/
theorem centreFloorBandList_eq_bandValList
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane} (hp : Function.Injective p)
    {i : V}
    (C : CentreProjectiveCycle hp i)
    {t : ℝ} (ht : 0 < t)
    (n : ℕ)
    (htop : t < (n + 1 : ℕ)) :
    centreFloorBandList C t =
      (centreProjectiveBandList C ht n htop).map Fin.val := by
  unfold centreFloorBandList scaledCentreAngles
  unfold CentreProjectiveCycle.angles
  simp only [floorBandList, List.map_map,
    centreProjectiveBandList]
  apply List.map_congr_left
  intro j hj
  change
    Nat.floor (normalizedRayTheta hp t i j) =
      (projectiveBandColor hp ht n htop i j.1).val
  symm
  exact projectiveBandColor_val
    hp ht n htop j.2.symm

/-- The toFinset cardinal of the natural band-index list is the number of
occupied projective bands. -/
theorem centreFloorBandList_toFinset_card_eq_occupied
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane} (hp : Function.Injective p)
    {i : V}
    (C : CentreProjectiveCycle hp i)
    {t : ℝ} (ht : 0 < t)
    (n : ℕ)
    (htop : t < (n + 1 : ℕ)) :
    (centreFloorBandList C t).toFinset.card =
      (occupiedProjectiveBands hp t n i).card := by
  classical
  rw [centreFloorBandList_eq_bandValList
      hp C ht n htop]
  have hmap :
      ((centreProjectiveBandList C ht n htop).map Fin.val).toFinset =
        (centreProjectiveBandList C ht n htop).toFinset.image Fin.val := by
    ext m
    simp
  rw [hmap,
      Finset.card_image_of_injective
        _ Fin.val_injective,
      ← occupiedProjectiveBands_eq_centreBandList_toFinset
        hp ht n htop i C]

theorem scaledCentreAngles_pairwise
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane} {hp : Function.Injective p} {i : V}
    (C : CentreProjectiveCycle hp i)
    {t : ℝ} (ht : 0 < t) :
    (scaledCentreAngles C t).Pairwise (· ≤ ·) := by
  unfold scaledCentreAngles
  rw [List.pairwise_map]
  intro a ha b hb hab
  unfold scaleProjectiveAngle
  have hpi : 0 < Real.pi := Real.pi_pos
  exact
    (div_le_div_iff_of_pos_right hpi).2
      (mul_le_mul_of_nonneg_left hab ht.le)

theorem scaledCentreAngles_mem_nonneg
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane} {hp : Function.Injective p} {i : V}
    (C : CentreProjectiveCycle hp i)
    {t : ℝ} (ht : 0 < t) :
    ∀ x ∈ scaledCentreAngles C t, 0 ≤ x := by
  intro x hx
  unfold scaledCentreAngles at hx
  obtain ⟨theta, htheta, rfl⟩ :=
    List.mem_map.mp hx
  have htheta0 :=
    (C.angle_mem_bounds htheta).1
  unfold scaleProjectiveAngle
  positivity

theorem scaledCentreAngles_mem_lt_t
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane} {hp : Function.Injective p} {i : V}
    (C : CentreProjectiveCycle hp i)
    {t : ℝ} (ht : 0 < t) :
    ∀ x ∈ scaledCentreAngles C t, x < t := by
  intro x hx
  unfold scaledCentreAngles at hx
  obtain ⟨theta, htheta, rfl⟩ :=
    List.mem_map.mp hx
  have hthetaPi :=
    (C.angle_mem_bounds htheta).2
  unfold scaleProjectiveAngle
  rw [div_lt_iff₀ Real.pi_pos]
  nlinarith [Real.pi_pos]

/-- Concrete centre quotient exponent is bounded by the cyclic empty-band
count of its scaled canonical rays. -/
theorem centreExponent_le_cyclicBandMissing
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane} {hp : Function.Injective p} {i : V}
    (C : CentreProjectiveCycle hp i)
    {t delta : ℝ} {n : ℕ}
    (htpos : 0 < t)
    (ht : t = (n : ℝ) + delta)
    (hdelta0 : 0 ≤ delta)
    (hdelta1 : delta < 1) :
    centreExponent C t ≤
      cyclicBandMissing (n + 1)
        (centreFloorBandList C t) := by
  obtain ⟨a, xs, hangles⟩ :
      ∃ a xs, C.angles = a :: xs := by
    cases h : C.angles with
    | nil =>
        exact False.elim (C.angles_nonempty h)
    | cons a xs =>
        exact ⟨a, xs, h⟩
  let A := scaleProjectiveAngle t a
  let XS := xs.map (scaleProjectiveAngle t)
  have hscaled :
      scaledCentreAngles C t = A :: XS := by
    simp [scaledCentreAngles, hangles, A, XS]
  have haMem : a ∈ C.angles := by
    rw [hangles]
    simp
  have hA0 : 0 ≤ A := by
    have ha0 := (C.angle_mem_bounds haMem).1
    dsimp [A, scaleProjectiveAngle]
    positivity
  have hsortedScaled :
      (A :: XS).Pairwise (· ≤ ·) := by
    rw [← hscaled]
    exact scaledCentreAngles_pairwise C htpos
  have hallScaled :
      ∀ x ∈ A :: XS, x < t := by
    intro x hx
    apply scaledCentreAngles_mem_lt_t C htpos
    rw [hscaled]
    exact hx
  have hcyc :=
    listExponent_floor_cyclicGaps_le_cyclicBandMissing
      A XS hA0 hsortedScaled hallScaled
      ht hdelta0 hdelta1
  have hquot :
      (cyclicGapsAt t
        ((a :: xs).map (scaleProjectiveAngle t))).map Nat.floor
        =
      quotientList t
        (normalizedProjectiveGaps (a :: xs)) :=
    floor_scaled_cyclicGaps_eq_quotientList
      t a xs
  have hscaledList :
      (a :: xs).map (scaleProjectiveAngle t) =
        A :: XS := by
    simp [A, XS]
  rw [← hscaledList] at hcyc
  rw [hquot] at hcyc
  have hgap :
      normalizedProjectiveGaps (a :: xs) = C.gaps := by
    simpa [CentreProjectiveCycle.gaps, hangles]
  rw [hgap,
      listExponent_quotientList_eq_centreExponent'] at hcyc
  have hfloor :
      floorBandList (A :: XS) =
        centreFloorBandList C t := by
    simpa [centreFloorBandList] using
      congrArg floorBandList hscaled.symm
  rwa [hfloor] at hcyc

/-- Main local budget: centre exponent is at most the number of missing
projective bands among n+1 bands. -/
theorem centreExponent_le_missing_projectiveBands
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane} (hp : Function.Injective p)
    {i : V}
    (C : CentreProjectiveCycle hp i)
    {t delta : ℝ} {n : ℕ}
    (htpos : 0 < t)
    (ht : t = (n : ℝ) + delta)
    (hdelta0 : 0 ≤ delta)
    (hdelta1 : delta < 1) :
    centreExponent C t ≤
      (n + 1) -
        (occupiedProjectiveBands hp t n i).card := by
  have htop : t < (n + 1 : ℕ) := by
    rw [ht]
    push_cast
    linarith
  have hexp :=
    centreExponent_le_cyclicBandMissing
      C htpos ht hdelta0 hdelta1
  obtain ⟨a, xs, hfloor⟩ :
      ∃ a xs, centreFloorBandList C t = a :: xs := by
    have hne : centreFloorBandList C t ≠ [] := by
      unfold centreFloorBandList floorBandList scaledCentreAngles
      simp [C.angles_nonempty]
    cases h : centreFloorBandList C t with
    | nil => exact False.elim (hne h)
    | cons a xs => exact ⟨a, xs, h⟩
  have hscaledSorted :
      (scaledCentreAngles C t).Pairwise (· ≤ ·) :=
    scaledCentreAngles_pairwise C htpos
  have hscaledNonneg :
      ∀ x ∈ scaledCentreAngles C t, 0 ≤ x :=
    scaledCentreAngles_mem_nonneg C htpos
  obtain ⟨A, XS, hscaled⟩ :
      ∃ A XS, scaledCentreAngles C t = A :: XS := by
    have hne : scaledCentreAngles C t ≠ [] := by
      unfold scaledCentreAngles
      simp [C.angles_nonempty]
    cases h : scaledCentreAngles C t with
    | nil => exact False.elim (hne h)
    | cons A XS => exact ⟨A, XS, h⟩
  have hA0 : 0 ≤ A :=
    hscaledNonneg A (by rw [hscaled]; simp)
  have hfloorSorted :
      (centreFloorBandList C t).Pairwise (· ≤ ·) := by
    unfold centreFloorBandList
    rw [hscaled]
    exact floorBandList_pairwise
      A XS hA0 (by
        rw [← hscaled]
        exact hscaledSorted)
  have hbound :
      ∀ m ∈ centreFloorBandList C t, m < n + 1 := by
    rw [centreFloorBandList_eq_bandValList
      hp C htpos n htop]
    intro m hm
    obtain ⟨c, hc, rfl⟩ := by
      simpa using (List.mem_map.mp hm)
    exact c.isLt
  have hmissing :
      cyclicBandMissing (n + 1)
          (centreFloorBandList C t)
        =
      (n + 1) -
        (centreFloorBandList C t).toFinset.card := by
    rw [hfloor] at hfloorSorted hbound ⊢
    exact cyclicBandMissing_eq_complement_card
      (n + 1) a xs hfloorSorted hbound
  rw [hmissing] at hexp
  rw [centreFloorBandList_toFinset_card_eq_occupied
      hp C htpos n htop] at hexp
  exact hexp

/-- Direct active-colour form for the global projective-band partition. -/
theorem projectiveBandPartition_active_card_le_deficit
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane} (hp : Function.Injective p)
    (hcap : AngleCap p lam)
    {t delta lam : ℝ} {n : ℕ}
    (htpos : 0 < t)
    (hlam : lam = Real.pi / t)
    (ht : t = (n : ℝ) + delta)
    (hdelta0 : 0 ≤ delta)
    (hdelta1 : delta < 1)
    (C : ∀ i : V, CentreProjectiveCycle hp i)
    (i : V) :
    (BinaryEdgePartition.active
      (projectiveBandPartition hp hcap htpos hlam n
        (by
          rw [ht]
          push_cast
          linarith))
      i).card
      ≤
    (n + 1) - centreExponent (C i) t := by
  let htop : t < (n + 1 : ℕ) := by
    rw [ht]
    push_cast
    linarith
  rw [projectiveBandPartition_active_card
      hp hcap htpos hlam n htop i]
  have hmissing :=
    centreExponent_le_missing_projectiveBands
      hp (C i) htpos ht hdelta0 hdelta1
  omega

#print axioms occupiedProjectiveBands_eq_centreBandList_toFinset
#print axioms centreFloorBandList_toFinset_card_eq_occupied
#print axioms centreExponent_le_cyclicBandMissing
#print axioms centreExponent_le_missing_projectiveBands
#print axioms projectiveBandPartition_active_card_le_deficit

end JSP000404Research
