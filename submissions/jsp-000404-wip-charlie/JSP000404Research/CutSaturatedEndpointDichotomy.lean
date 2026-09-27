import JSP000404Research.SaturatedSeamPhaseArithmetic
import JSP000404Research.CutLocalBandCycle
import JSP000404Research.CutProjectiveBandBudget
import JSP000404Research.LinearSaturatedEndpointDichotomy
import Mathlib.Tactic

/-!
# Saturated endpoint dichotomy for an arbitrary projective cut

Let R be the cut-sorted ray cycle at one centre.  CutLocalBandCycle identifies

  R.exponent = centreExponent

and identifies the distinct floors of R.normalizedValues with the active
colours of cutProjectiveBandPartition.

Hence exact saturation of the full (n+1)-band local budget is literally the
one-dimensional equality

  cyclic gap exponent + occupied band count = n+1.

If the top band n is active, LinearSaturatedEndpointDichotomy applies.  Either
band zero is also active, so the 0/n last merge really drops one local colour,
or the cut-sorted value profile contains a zero-quotient crossing of one unit
band boundary.

This isolates the only remaining unsafe saturated mechanism at arbitrary cut.
-/

namespace JSP000404Research

open BinaryEdgePartition

namespace CentreCutRayCycle

/-- Active top colour gives an actual cut-sorted local value of natural floor
n. -/
theorem exists_normalizedValue_floor_eq_top_of_top_active
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane} (hp : Function.Injective p)
    (hcap : AngleCap p lam)
    {lam t c : ℝ}
    (ht : 0 < t)
    (hlam : lam = Real.pi / t)
    (hc0 : 0 ≤ c) (hcpi : c < Real.pi)
    (n : ℕ)
    (htop : t < (n + 1 : ℕ))
    {i : V}
    (C : CentreProjectiveCycle hp i)
    (R : CentreCutRayCycle hp C c)
    (hTopActive :
      (Fin.last n) ∈
        active
          (cutProjectiveBandPartition
            hp hcap ht hlam hc0 hcpi n htop)
          i) :
    ∃ x ∈ R.normalizedValues t,
      Nat.floor x = n := by
  have hocc :
      (Fin.last n) ∈
        occupiedCutProjectiveBands hp t c n i := by
    rw [← cutProjectiveBandPartition_active_eq_occupied
      hp hcap ht hlam hc0 hcpi n htop i]
    exact hTopActive
  obtain ⟨j, hjBand⟩ :=
    (mem_occupiedCutProjectiveBands
      hp t c n i (Fin.last n)).1 hocc
  let x := cutNormalizedRayTheta hp t c i j
  have hxMem : x ∈ R.normalizedValues t := by
    unfold CentreCutRayCycle.normalizedValues
    apply List.mem_map.mpr
    exact ⟨j, R.mem_rays j, rfl⟩
  have hx0 : 0 ≤ x :=
    cutNormalizedRayTheta_nonneg
      hp ht.le hc0 hcpi i j
  have hfloor :
      Nat.floor x = n := by
    apply (Nat.floor_eq_iff hx0).2
    have hlo : (n : ℝ) ≤ x := by
      simpa [x, RayInCutProjectiveBand] using hjBand.1
    have hhi : x < (n : ℝ) + 1 := by
      simpa [x, RayInCutProjectiveBand] using hjBand.2
    exact ⟨hlo, hhi⟩
  exact ⟨x, hxMem, hfloor⟩

/-- Any cut-sorted local value whose floor is b.val makes b an active
partition colour at the centre. -/
theorem active_of_normalizedValue_floor
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane} (hp : Function.Injective p)
    (hcap : AngleCap p lam)
    {lam t c : ℝ}
    (ht : 0 < t)
    (hlam : lam = Real.pi / t)
    (hc0 : 0 ≤ c) (hcpi : c < Real.pi)
    (n : ℕ)
    (htop : t < (n + 1 : ℕ))
    {i : V}
    (C : CentreProjectiveCycle hp i)
    (R : CentreCutRayCycle hp C c)
    (b : Fin (n + 1))
    (hmem :
      ∃ x ∈ R.normalizedValues t,
        Nat.floor x = b.val) :
    b ∈
      active
        (cutProjectiveBandPartition
          hp hcap ht hlam hc0 hcpi n htop)
        i := by
  obtain ⟨x, hx, hfloor⟩ := hmem
  unfold CentreCutRayCycle.normalizedValues at hx
  obtain ⟨j, hjR, hjx⟩ := List.mem_map.mp hx
  have hx0 :
      0 ≤ cutNormalizedRayTheta hp t c i j :=
    cutNormalizedRayTheta_nonneg
      hp ht.le hc0 hcpi i j
  have hlo :
      (b.val : ℝ) ≤
        cutNormalizedRayTheta hp t c i j := by
    have h := Nat.floor_le hx0
    rw [hfloor] at h
    exact h
  have hhi :
      cutNormalizedRayTheta hp t c i j <
        (b.val : ℝ) + 1 := by
    have h :=
      Nat.lt_floor_add_one
        (cutNormalizedRayTheta hp t c i j)
    rw [hfloor] at h
    exact h
  have hocc :
      b ∈ occupiedCutProjectiveBands hp t c n i := by
    apply (mem_occupiedCutProjectiveBands
      hp t c n i b).2
    exact ⟨j, ⟨by simpa using hlo, by simpa using hhi⟩⟩
  rw [cutProjectiveBandPartition_active_eq_occupied
    hp hcap ht hlam hc0 hcpi n htop i]
  exact hocc

/-- Exact active-card saturation is the exact one-dimensional local equality
for the cut-sorted values. -/
theorem local_band_equality_of_active_saturated
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane} (hp : Function.Injective p)
    (hcap : AngleCap p lam)
    {lam t c : ℝ}
    (ht : 0 < t)
    (hlam : lam = Real.pi / t)
    (hc0 : 0 ≤ c) (hcpi : c < Real.pi)
    (n : ℕ)
    (htop : t < (n + 1 : ℕ))
    {i : V}
    (C : CentreProjectiveCycle hp i)
    (R : CentreCutRayCycle hp C c)
    (hsat :
      centreExponent C t +
        (active
          (cutProjectiveBandPartition
            hp hcap ht hlam hc0 hcpi n htop)
          i).card
        =
      n + 1) :
    R.exponent t +
        (occupiedNatBands (R.normalizedValues t)).card
      =
    n + 1 := by
  rw [R.exponent_eq_centreExponent hp ht]
  rw [R.occupiedNatBands_normalizedValues_card_eq_occupiedCut
      hp ht hc0 hcpi n htop]
  rw [← cutProjectiveBandPartition_active_eq_occupied
      hp hcap ht hlam hc0 hcpi n htop i]
  exact hsat

/-- Main arbitrary-cut saturation dichotomy, stated on the cut-sorted value
list. -/
theorem saturated_topBand_zeroFirst_or_zeroUnitStep
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane} (hp : Function.Injective p)
    (hcap : AngleCap p lam)
    {lam t delta c : ℝ} {n : ℕ}
    (hn : 1 ≤ n)
    (htpos : 0 < t)
    (hlam : lam = Real.pi / t)
    (ht : t = (n : ℝ) + delta)
    (hdeltaHalf : delta < (1 : ℝ) / 2)
    (hc0 : 0 ≤ c) (hcpi : c < Real.pi)
    {i : V}
    (C : CentreProjectiveCycle hp i)
    (R : CentreCutRayCycle hp C c)
    (hsat :
      centreExponent C t +
        (active
          (cutProjectiveBandPartition
            hp hcap htpos hlam hc0 hcpi n
              (by rw [ht]; push_cast; linarith))
          i).card
        =
      n + 1)
    (hTopActive :
      (Fin.last n) ∈
        active
          (cutProjectiveBandPartition
            hp hcap htpos hlam hc0 hcpi n
              (by rw [ht]; push_cast; linarith))
          i) :
    ∃ a xs,
      R.normalizedValues t = a :: xs ∧
      (Nat.floor a = 0 ∨
        HasZeroQuotientUnitStep a xs) := by
  obtain ⟨a, xs, hvalues⟩ :
      ∃ a xs, R.normalizedValues t = a :: xs := by
    cases h : R.normalizedValues t with
    | nil =>
        exact False.elim (R.normalizedValues_nonempty t h)
    | cons a xs =>
        exact ⟨a, xs, h⟩
  have haMem : a ∈ R.normalizedValues t := by
    rw [hvalues]
    simp
  have ha0 :
      0 ≤ a :=
    (R.normalizedValues_mem_bounds
      htpos hc0 hcpi haMem).1
  have hsorted :
      (a :: xs).Pairwise (· ≤ ·) := by
    simpa [hvalues] using
      R.normalizedValues_pairwise htpos.le
  have hall :
      ∀ x ∈ a :: xs, x < t := by
    intro x hx
    exact
      (R.normalizedValues_mem_bounds
        htpos hc0 hcpi
        (by simpa [hvalues] using hx)).2
  have heqR :=
    R.local_band_equality_of_active_saturated
      hp hcap htpos hlam hc0 hcpi n
      (by rw [ht]; push_cast; linarith)
      hsat
  have heq :
      listExponent
          (linearCyclicGapQuotients t (a :: xs)) +
        (occupiedNatBands (a :: xs)).card
        =
      n + 1 := by
    simpa [CentreCutRayCycle.exponent,
      CentreCutRayCycle.gapQuotients, hvalues] using heqR
  have htopVal :=
    R.exists_normalizedValue_floor_eq_top_of_top_active
      hp hcap htpos hlam hc0 hcpi n
      (by rw [ht]; push_cast; linarith)
      hTopActive
  have htopMem :
      ∃ x ∈ a :: xs, Nat.floor x = n := by
    simpa [hvalues] using htopVal
  have hdich :=
    JSP000404Research.saturated_topBand_zeroFirst_or_zeroUnitStep
      a xs ha0 hsorted hall ht hdeltaHalf heq htopMem
  exact ⟨a, xs, hvalues, hdich⟩

/-- Strong arbitrary-cut form: every saturated centre either really occupies
both colours merged by 0/n, or its cut-sorted profile contains a zero-quotient
unit-band crossing. -/
theorem saturated_boundaryActive_or_zeroUnitStep
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane} (hp : Function.Injective p)
    (hcap : AngleCap p lam)
    {lam t delta c : ℝ} {n : ℕ}
    (hn : 1 ≤ n)
    (htpos : 0 < t)
    (hlam : lam = Real.pi / t)
    (ht : t = (n : ℝ) + delta)
    (hdeltaHalf : delta < (1 : ℝ) / 2)
    (hc0 : 0 ≤ c) (hcpi : c < Real.pi)
    {i : V}
    (C : CentreProjectiveCycle hp i)
    (R : CentreCutRayCycle hp C c)
    (hsat :
      centreExponent C t +
        (active
          (cutProjectiveBandPartition
            hp hcap htpos hlam hc0 hcpi n
              (by rw [ht]; push_cast; linarith))
          i).card
        =
      n + 1) :
    (
      (0 : Fin (n + 1)) ∈
        active
          (cutProjectiveBandPartition
            hp hcap htpos hlam hc0 hcpi n
              (by rw [ht]; push_cast; linarith))
          i
      ∧
      Fin.last n ∈
        active
          (cutProjectiveBandPartition
            hp hcap htpos hlam hc0 hcpi n
              (by rw [ht]; push_cast; linarith))
          i
    )
    ∨
    (
      ∃ a xs,
        R.normalizedValues t = a :: xs ∧
        HasZeroQuotientUnitStep a xs
    ) := by
  obtain ⟨a, xs, hvalues⟩ :
      ∃ a xs, R.normalizedValues t = a :: xs := by
    cases h : R.normalizedValues t with
    | nil =>
        exact False.elim (R.normalizedValues_nonempty t h)
    | cons a xs =>
        exact ⟨a, xs, h⟩
  have haMem : a ∈ R.normalizedValues t := by
    rw [hvalues]
    simp
  have ha0 :
      0 ≤ a :=
    (R.normalizedValues_mem_bounds
      htpos hc0 hcpi haMem).1
  have hsorted :
      (a :: xs).Pairwise (· ≤ ·) := by
    simpa [hvalues] using
      R.normalizedValues_pairwise htpos.le
  have hall :
      ∀ x ∈ a :: xs, x < t := by
    intro x hx
    exact
      (R.normalizedValues_mem_bounds
        htpos hc0 hcpi
        (by simpa [hvalues] using hx)).2
  have heqR :=
    R.local_band_equality_of_active_saturated
      hp hcap htpos hlam hc0 hcpi n
      (by rw [ht]; push_cast; linarith)
      hsat
  have heq :
      listExponent
          (linearCyclicGapQuotients t (a :: xs)) +
        (occupiedNatBands (a :: xs)).card
        =
      n + 1 := by
    simpa [CentreCutRayCycle.exponent,
      CentreCutRayCycle.gapQuotients, hvalues] using heqR
  rcases JSP000404Research.saturated_boundaryBands_or_zeroUnitStep
      a xs ha0 hsorted hall ht hdeltaHalf heq
    with hboundary | hstep
  · left
    let htop : t < (n + 1 : ℕ) := by
      rw [ht]
      push_cast
      linarith
    have hzeroMem :
        ∃ x ∈ R.normalizedValues t,
          Nat.floor x = (0 : Fin (n + 1)).val := by
      refine ⟨a, ?_, ?_⟩
      · rw [hvalues]
        simp
      · simpa using hboundary.1
    have hlastMem :
        ∃ x ∈ R.normalizedValues t,
          Nat.floor x = (Fin.last n).val := by
      let z := xs.getLastD a
      refine ⟨z, ?_, ?_⟩
      · rw [hvalues]
        exact List.getLastD_mem_cons a xs
      · simpa using hboundary.2
    exact ⟨
      R.active_of_normalizedValue_floor
        hp hcap htpos hlam hc0 hcpi n htop
        (0 : Fin (n + 1)) hzeroMem,
      R.active_of_normalizedValue_floor
        hp hcap htpos hlam hc0 hcpi n htop
        (Fin.last n) hlastMem⟩
  · right
    exact ⟨a, xs, hvalues, hstep⟩

/-- Contrapositive form used by the last merge: a saturated centre at which
the 0/n merge does not collide must carry a zero-quotient unit step. -/
theorem zeroUnitStep_of_saturated_boundary_collision_failure
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane} (hp : Function.Injective p)
    (hcap : AngleCap p lam)
    {lam t delta c : ℝ} {n : ℕ}
    (hn : 1 ≤ n)
    (htpos : 0 < t)
    (hlam : lam = Real.pi / t)
    (ht : t = (n : ℝ) + delta)
    (hdeltaHalf : delta < (1 : ℝ) / 2)
    (hc0 : 0 ≤ c) (hcpi : c < Real.pi)
    {i : V}
    (C : CentreProjectiveCycle hp i)
    (R : CentreCutRayCycle hp C c)
    (hsat :
      centreExponent C t +
        (active
          (cutProjectiveBandPartition
            hp hcap htpos hlam hc0 hcpi n
              (by rw [ht]; push_cast; linarith))
          i).card
        =
      n + 1)
    (hfail :
      ¬ (
        (0 : Fin (n + 1)) ∈
          active
            (cutProjectiveBandPartition
              hp hcap htpos hlam hc0 hcpi n
                (by rw [ht]; push_cast; linarith))
            i
        ∧
        Fin.last n ∈
          active
            (cutProjectiveBandPartition
              hp hcap htpos hlam hc0 hcpi n
                (by rw [ht]; push_cast; linarith))
            i
      )) :
    ∃ a xs,
      R.normalizedValues t = a :: xs ∧
      HasZeroQuotientUnitStep a xs := by
  rcases R.saturated_boundaryActive_or_zeroUnitStep
      hp hcap hn htpos hlam ht hdeltaHalf
      hc0 hcpi hsat with hboundary | hstep
  · exact False.elim (hfail hboundary)
  · exact hstep

/-- Exact seam data extracted from a saturated centre at which the 0/n
boundary collision fails.  The wrap gap contains a canonical whole-unit
subslot indexed by j, and the cut position lies in its delta-width bad
window. -/
theorem saturated_failure_has_wrap_unit_subslot_data
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane} (hp : Function.Injective p)
    (hcap : AngleCap p lam)
    {lam t delta c : ℝ} {n : ℕ}
    (hn : 1 ≤ n)
    (htpos : 0 < t)
    (hlam : lam = Real.pi / t)
    (ht : t = (n : ℝ) + delta)
    (hdelta0 : 0 ≤ delta)
    (hdeltaHalf : delta < (1 : ℝ) / 2)
    (hc0 : 0 ≤ c) (hcpi : c < Real.pi)
    {i : V}
    (C : CentreProjectiveCycle hp i)
    (R : CentreCutRayCycle hp C c)
    (hsat :
      centreExponent C t +
        (active
          (cutProjectiveBandPartition
            hp hcap htpos hlam hc0 hcpi n
              (by rw [ht]; push_cast; linarith))
          i).card
        =
      n + 1)
    (hfail :
      ¬ (
        (0 : Fin (n + 1)) ∈
          active
            (cutProjectiveBandPartition
              hp hcap htpos hlam hc0 hcpi n
                (by rw [ht]; push_cast; linarith))
            i
        ∧
        Fin.last n ∈
          active
            (cutProjectiveBandPartition
              hp hcap htpos hlam hc0 hcpi n
                (by rw [ht]; push_cast; linarith))
            i
      )) :
    ∃ a xs,
      R.normalizedValues t = a :: xs ∧
      let z := xs.getLastD a
      let s := a + t - z
      let q := Nat.floor s
      let j := saturatedSeamIndex n z
      2 ≤ q ∧
        j < q ∧
        ((j : ℝ) + s - (q : ℝ) < t - z) ∧
        (t - z ≤ (j : ℝ) + delta) := by
  obtain ⟨a, xs, hvalues⟩ :
      ∃ a xs, R.normalizedValues t = a :: xs := by
    cases h : R.normalizedValues t with
    | nil =>
        exact False.elim (R.normalizedValues_nonempty t h)
    | cons a xs =>
        exact ⟨a, xs, h⟩
  have haMem : a ∈ R.normalizedValues t := by
    rw [hvalues]
    simp
  have ha0 :
      0 ≤ a :=
    (R.normalizedValues_mem_bounds
      htpos hc0 hcpi haMem).1
  have hsorted :
      (a :: xs).Pairwise (· ≤ ·) := by
    simpa [hvalues] using
      R.normalizedValues_pairwise htpos.le
  have hall :
      ∀ x ∈ a :: xs, x < t := by
    intro x hx
    exact
      (R.normalizedValues_mem_bounds
        htpos hc0 hcpi
        (by simpa [hvalues] using hx)).2
  let z := xs.getLastD a
  have haz : a ≤ z :=
    head_le_getLastD_of_pairwise a xs hsorted
  have hzt : z < t :=
    hall z (List.getLastD_mem_cons a xs)
  have heqR :=
    R.local_band_equality_of_active_saturated
      hp hcap htpos hlam hc0 hcpi n
      (by rw [ht]; push_cast; linarith)
      hsat
  have heq :
      listExponent
          (linearCyclicGapQuotients t (a :: xs)) +
        (occupiedNatBands (a :: xs)).card
        =
      n + 1 := by
    simpa [CentreCutRayCycle.exponent,
      CentreCutRayCycle.gapQuotients, hvalues] using heqR
  have hwrap :
      excess (Nat.floor (a + t - z)) =
        n - Nat.floor z + Nat.floor a := by
    have htTop : t < (n : ℝ) + 1 := by
      rw [ht]
      linarith
    simpa [z] using
      wrap_gap_excess_eq_outer_empty_of_global_equality
        a xs ha0 hsorted hall htTop heq
  have hfloorFail :
      ¬ (Nat.floor a = 0 ∧ Nat.floor z = n) := by
    intro hb
    have htop : t < (n + 1 : ℕ) := by
      rw [ht]
      push_cast
      linarith
    have hzeroMem :
        ∃ x ∈ R.normalizedValues t,
          Nat.floor x = (0 : Fin (n + 1)).val := by
      exact ⟨a, by rw [hvalues]; simp, by simpa using hb.1⟩
    have hlastMem :
        ∃ x ∈ R.normalizedValues t,
          Nat.floor x = (Fin.last n).val := by
      exact ⟨z,
        by rw [hvalues]; exact List.getLastD_mem_cons a xs,
        by simpa [z] using hb.2⟩
    apply hfail
    exact ⟨
      R.active_of_normalizedValue_floor
        hp hcap htpos hlam hc0 hcpi n htop
        (0 : Fin (n + 1)) hzeroMem,
      R.active_of_normalizedValue_floor
        hp hcap htpos hlam hc0 hcpi n htop
        (Fin.last n) hlastMem⟩
  have hseam :=
    saturated_wrap_failure_unit_subslot
      ha0 haz hzt ht hdelta0
      (by linarith : delta < 1)
      rfl hwrap hfloorFail
  refine ⟨a, xs, hvalues, ?_⟩
  simpa [z] using hseam

/-- If top is active but zero is not, an exact saturated cut centre necessarily
carries a zero-quotient unit-band crossing. -/
theorem saturated_top_without_zero_forces_zeroUnitStep
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane} (hp : Function.Injective p)
    (hcap : AngleCap p lam)
    {lam t delta c : ℝ} {n : ℕ}
    (hn : 1 ≤ n)
    (htpos : 0 < t)
    (hlam : lam = Real.pi / t)
    (ht : t = (n : ℝ) + delta)
    (hdeltaHalf : delta < (1 : ℝ) / 2)
    (hc0 : 0 ≤ c) (hcpi : c < Real.pi)
    {i : V}
    (C : CentreProjectiveCycle hp i)
    (R : CentreCutRayCycle hp C c)
    (hsat :
      centreExponent C t +
        (active
          (cutProjectiveBandPartition
            hp hcap htpos hlam hc0 hcpi n
              (by rw [ht]; push_cast; linarith))
          i).card
        =
      n + 1)
    (hTopActive :
      (Fin.last n) ∈
        active
          (cutProjectiveBandPartition
            hp hcap htpos hlam hc0 hcpi n
              (by rw [ht]; push_cast; linarith))
          i)
    (hZeroNotActive :
      (0 : Fin (n + 1)) ∉
        active
          (cutProjectiveBandPartition
            hp hcap htpos hlam hc0 hcpi n
              (by rw [ht]; push_cast; linarith))
          i) :
    ∃ a xs,
      R.normalizedValues t = a :: xs ∧
      HasZeroQuotientUnitStep a xs := by
  obtain ⟨a, xs, hvalues, hzero | hstep⟩ :=
    R.saturated_topBand_zeroFirst_or_zeroUnitStep
      hp hcap hn htpos hlam ht hdeltaHalf
      hc0 hcpi hsat hTopActive
  · exfalso
    have haMem : a ∈ R.normalizedValues t := by
      rw [hvalues]
      simp
    have haFloor : Nat.floor a = 0 := hzero
    obtain ⟨j, hjRay, hjVal⟩ :
        ∃ j ∈ R.rays,
          cutNormalizedRayTheta hp t c i j = a := by
      unfold CentreCutRayCycle.normalizedValues at haMem
      obtain ⟨j, hj, hja⟩ := List.mem_map.mp haMem
      exact ⟨j, hj, hja⟩
    let b0 : Fin (n + 1) := 0
    have hjBand :
        RayInCutProjectiveBand hp t c i j b0 := by
      unfold RayInCutProjectiveBand
      have hx0 :=
        cutNormalizedRayTheta_nonneg
          hp htpos.le hc0 hcpi i j
      have hhi :=
        Nat.lt_floor_add_one
          (cutNormalizedRayTheta hp t c i j)
      have hfloorJ :
          Nat.floor (cutNormalizedRayTheta hp t c i j) = 0 := by
        rw [hjVal, haFloor]
      rw [hfloorJ] at hhi
      constructor
      · simpa [b0] using hx0
      · simpa [b0] using hhi
    have hocc :
        b0 ∈ occupiedCutProjectiveBands hp t c n i :=
      (mem_occupiedCutProjectiveBands
        hp t c n i b0).2 ⟨j, hjBand⟩
    have hactive :
        b0 ∈
          active
            (cutProjectiveBandPartition
              hp hcap htpos hlam hc0 hcpi n
                (by rw [ht]; push_cast; linarith))
            i := by
      rw [cutProjectiveBandPartition_active_eq_occupied
        hp hcap htpos hlam hc0 hcpi n
          (by rw [ht]; push_cast; linarith) i]
      exact hocc
    exact hZeroNotActive hactive
  · exact ⟨a, xs, hvalues, hstep⟩

#print axioms CentreCutRayCycle.local_band_equality_of_active_saturated
#print axioms CentreCutRayCycle.saturated_topBand_zeroFirst_or_zeroUnitStep
#print axioms CentreCutRayCycle.saturated_top_without_zero_forces_zeroUnitStep

end CentreCutRayCycle
end JSP000404Research
