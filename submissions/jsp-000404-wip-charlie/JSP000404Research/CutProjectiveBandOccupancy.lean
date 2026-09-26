import JSP000404Research.CutProjectiveBandPartition
import JSP000404Research.BinaryEdgePartition
import Mathlib.Tactic

/-!
# Occupied bands for the arbitrary-cut projective partition

This is the cut-rotated analogue of ProjectiveBandOccupancy.

At a centre i, a colour is active in cutProjectiveBandPartition exactly when
some concrete ray from i occupies that cut unit band.  Consequently the active
cardinality is the number of distinct natural floor labels of the
cut-normalized ray coordinates.
-/

namespace JSP000404Research

open BinaryEdgePartition

def occupiedCutProjectiveBands
    {V : Type*} {p : V → Plane}
    (hp : Function.Injective p)
    (t c : ℝ) (n : ℕ) (i : V) :
    Finset (Fin (n + 1)) :=
  Finset.univ.filter fun b =>
    ∃ j : OtherVertex i,
      RayInCutProjectiveBand hp t c i j b

theorem mem_occupiedCutProjectiveBands
    {V : Type*} {p : V → Plane}
    (hp : Function.Injective p)
    (t c : ℝ) (n : ℕ) (i : V)
    (b : Fin (n + 1)) :
    b ∈ occupiedCutProjectiveBands hp t c n i ↔
      ∃ j : OtherVertex i,
        RayInCutProjectiveBand hp t c i j b := by
  simp [occupiedCutProjectiveBands]

theorem cutProjectiveBandColor_eq_of_ray_mem
    {V : Type*} {p : V → Plane}
    (hp : Function.Injective p)
    {t c : ℝ} (ht : 0 < t)
    (hc0 : 0 ≤ c) (hcpi : c < Real.pi)
    (n : ℕ)
    (htop : t < (n + 1 : ℕ))
    {i : V} (j : OtherVertex i)
    (b : Fin (n + 1))
    (hj : RayInCutProjectiveBand hp t c i j b) :
    cutProjectiveBandColor hp ht hc0 hcpi n htop i j.1 = b := by
  apply Fin.ext
  rw [cutProjectiveBandColor_val
      hp ht hc0 hcpi n htop j.2.symm]
  have hx0 :=
    cutNormalizedRayTheta_nonneg
      hp ht.le hc0 hcpi i j
  have hfloorLo :
      b.val ≤
        Nat.floor (cutNormalizedRayTheta hp t c i j) := by
    exact (Nat.le_floor hx0).2 (by
      exact_mod_cast hj.1)
  have hfloorHi :
      Nat.floor (cutNormalizedRayTheta hp t c i j) < b.val + 1 := by
    apply (Nat.floor_lt hx0).2
    simpa using hj.2
  omega

/-- Active colours equal occupied cut bands. -/
theorem cutProjectiveBandPartition_active_eq_occupied
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane}
    (hp : Function.Injective p)
    (hcap : AngleCap p lam)
    {t lam c : ℝ}
    (ht : 0 < t)
    (hlam : lam = Real.pi / t)
    (hc0 : 0 ≤ c) (hcpi : c < Real.pi)
    (n : ℕ)
    (htop : t < (n + 1 : ℕ))
    (i : V) :
    active
        (cutProjectiveBandPartition
          hp hcap ht hlam hc0 hcpi n htop)
        i
      =
    occupiedCutProjectiveBands hp t c n i := by
  classical
  ext b
  constructor
  · intro hb
    rw [mem_active_iff] at hb
    obtain ⟨j, hji, hcol⟩ := hb
    let r : OtherVertex i := ⟨j, hji.symm⟩
    have hrBand :
        RayInCutProjectiveBand hp t c i r
          (cutProjectiveBandColor
            hp ht hc0 hcpi n htop i j) :=
      cutProjectiveBandColor_mem_lower
        hp ht hc0 hcpi n htop hji.symm
    apply (mem_occupiedCutProjectiveBands
      hp t c n i b).2
    refine ⟨r, ?_⟩
    simpa [cutProjectiveBandPartition] using
      (show
        RayInCutProjectiveBand hp t c i r
          (cutProjectiveBandColor
            hp ht hc0 hcpi n htop i j) from hrBand)
        |>.trans ?_
    · exact hrBand
  · intro hb
    obtain ⟨j, hjBand⟩ :=
      (mem_occupiedCutProjectiveBands
        hp t c n i b).1 hb
    rw [mem_active_iff]
    refine ⟨j.1, j.2, ?_⟩
    have hcol :=
      cutProjectiveBandColor_eq_of_ray_mem
        hp ht hc0 hcpi n htop j b hjBand
    simpa [cutProjectiveBandPartition] using hcol

noncomputable def cutRayProjectiveBand
    {V : Type*} {p : V → Plane}
    (hp : Function.Injective p)
    {t c : ℝ} (ht : 0 < t)
    (hc0 : 0 ≤ c) (hcpi : c < Real.pi)
    (n : ℕ)
    (htop : t < (n + 1 : ℕ))
    (i : V) (j : OtherVertex i) :
    Fin (n + 1) :=
  cutProjectiveBandColor hp ht hc0 hcpi n htop i j.1

noncomputable def cutCentreBandList
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane} {hp : Function.Injective p} {i : V}
    (C : CentreProjectiveCycle hp i)
    {t c : ℝ} (ht : 0 < t)
    (hc0 : 0 ≤ c) (hcpi : c < Real.pi)
    (n : ℕ)
    (htop : t < (n + 1 : ℕ)) :
    List (Fin (n + 1)) :=
  C.rays.map
    (cutRayProjectiveBand hp ht hc0 hcpi n htop i)

def cutFloorBandList
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane} {hp : Function.Injective p} {i : V}
    (C : CentreProjectiveCycle hp i)
    (t c : ℝ) : List ℕ :=
  C.rays.map fun j =>
    Nat.floor (cutNormalizedRayTheta hp t c i j)

theorem cutFloorBandList_eq_bandValList
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane} (hp : Function.Injective p)
    {i : V}
    (C : CentreProjectiveCycle hp i)
    {t c : ℝ} (ht : 0 < t)
    (hc0 : 0 ≤ c) (hcpi : c < Real.pi)
    (n : ℕ)
    (htop : t < (n + 1 : ℕ)) :
    cutFloorBandList C t c =
      (cutCentreBandList C ht hc0 hcpi n htop).map Fin.val := by
  unfold cutFloorBandList cutCentreBandList
  rw [List.map_map]
  apply List.map_congr_left
  intro j hj
  change
    Nat.floor (cutNormalizedRayTheta hp t c i j) =
      (cutProjectiveBandColor hp ht hc0 hcpi n htop i j.1).val
  symm
  exact cutProjectiveBandColor_val
    hp ht hc0 hcpi n htop j.2.symm

theorem occupiedCutProjectiveBands_eq_centreBandList_toFinset
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane} (hp : Function.Injective p)
    {t c : ℝ} (ht : 0 < t)
    (hc0 : 0 ≤ c) (hcpi : c < Real.pi)
    (n : ℕ)
    (htop : t < (n + 1 : ℕ))
    (i : V)
    (C : CentreProjectiveCycle hp i) :
    occupiedCutProjectiveBands hp t c n i =
      (cutCentreBandList C ht hc0 hcpi n htop).toFinset := by
  classical
  ext b
  constructor
  · intro hb
    obtain ⟨j, hjBand⟩ :=
      (mem_occupiedCutProjectiveBands
        hp t c n i b).1 hb
    have hjRay : j ∈ C.rays := C.mem_rays_iff j
    have hcol :=
      cutProjectiveBandColor_eq_of_ray_mem
        hp ht hc0 hcpi n htop j b hjBand
    simp only [cutCentreBandList, List.mem_toFinset,
      List.mem_map]
    exact ⟨j, hjRay, hcol⟩
  · intro hb
    have hbList :
        b ∈ cutCentreBandList C ht hc0 hcpi n htop := by
      simpa using hb
    obtain ⟨j, hjRay, hjeq⟩ := by
      simpa [cutCentreBandList] using hbList
    apply (mem_occupiedCutProjectiveBands
      hp t c n i b).2
    refine ⟨j, ?_⟩
    rw [← hjeq]
    unfold RayInCutProjectiveBand
    rw [cutProjectiveBandColor_val
      hp ht hc0 hcpi n htop j.2.symm]
    exact ⟨
      Nat.floor_le
        (cutNormalizedRayTheta_nonneg
          hp ht.le hc0 hcpi i j),
      Nat.lt_floor_add_one _⟩

theorem cutFloorBandList_toFinset_card_eq_occupied
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane} (hp : Function.Injective p)
    {i : V}
    (C : CentreProjectiveCycle hp i)
    {t c : ℝ} (ht : 0 < t)
    (hc0 : 0 ≤ c) (hcpi : c < Real.pi)
    (n : ℕ)
    (htop : t < (n + 1 : ℕ)) :
    (cutFloorBandList C t c).toFinset.card =
      (occupiedCutProjectiveBands hp t c n i).card := by
  classical
  rw [cutFloorBandList_eq_bandValList
      hp C ht hc0 hcpi n htop]
  have hmap :
      ((cutCentreBandList C ht hc0 hcpi n htop).map
        Fin.val).toFinset =
      (cutCentreBandList C ht hc0 hcpi n htop).toFinset.image
        Fin.val := by
    ext m
    simp
  rw [hmap,
      Finset.card_image_of_injective _ Fin.val_injective,
      ← occupiedCutProjectiveBands_eq_centreBandList_toFinset
        hp ht hc0 hcpi n htop i C]

#print axioms cutProjectiveBandPartition_active_eq_occupied
#print axioms cutFloorBandList_toFinset_card_eq_occupied

end JSP000404Research
