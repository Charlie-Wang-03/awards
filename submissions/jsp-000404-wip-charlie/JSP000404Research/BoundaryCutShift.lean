import JSP000404Research.CutProjectiveBandPartition
import JSP000404Research.CyclicCriticalUnitPhase
import Mathlib.Tactic

/-!
# Shifting a projective cut from a merge seam to its short boundary arc

For a partition cut cP, the merged boundary colours are the cyclic union

  [0,1) ∪ [n,t),    t = n + delta.

This is one projective arc of normalized length 1+delta whose cyclic start is
the old coordinate n.  Move the projective cut backwards by delta cap units:

  d  = delta*pi/t,
  cS = cP-d              if d <= cP,
       cP+pi-d           otherwise.

Then every normalized cut coordinate transforms by the circle rotation

  xS = xP + delta        when xP < n,
       xP - n            when n <= xP.

Hence old boundary bands 0 and n both land in [0,1+delta) at cS.

The corresponding global phase is unchanged modulo the period t:

  t*cS/pi + delta = t*cP/pi          or
                    t*cP/pi + t.

This is the algebraic seam bridge between cutProjectiveBandPartition and the
short-cut critical-slot machinery.
-/

namespace JSP000404Research

open Real

def shiftBackProjectiveCut (c d : ℝ) : ℝ :=
  if d ≤ c then c - d else c + Real.pi - d

theorem shiftBackProjectiveCut_nonneg
    {c d : ℝ}
    (hc0 : 0 ≤ c)
    (hcpi : c < Real.pi)
    (hd0 : 0 ≤ d)
    (hdpi : d < Real.pi) :
    0 ≤ shiftBackProjectiveCut c d := by
  unfold shiftBackProjectiveCut
  split_ifs with h
  · linarith
  · have hcd : c < d := lt_of_not_ge h
    linarith

theorem shiftBackProjectiveCut_lt_pi
    {c d : ℝ}
    (hc0 : 0 ≤ c)
    (hcpi : c < Real.pi)
    (hd0 : 0 ≤ d)
    (hdpi : d < Real.pi) :
    shiftBackProjectiveCut c d < Real.pi := by
  unfold shiftBackProjectiveCut
  split_ifs with h
  · linarith
  · have hcd : c < d := lt_of_not_ge h
    linarith

/-- Circle-rotation formula below the shifted seam. -/
theorem cutRayTheta_shiftBack_of_lt
    {V : Type*} {p : V → Plane}
    (hp : Function.Injective p)
    {c d : ℝ}
    (hc0 : 0 ≤ c) (hcpi : c < Real.pi)
    (hd0 : 0 ≤ d) (hdpi : d < Real.pi)
    (i : V) (j : OtherVertex i)
    (hgap :
      cutRayTheta hp c i j < Real.pi - d) :
    cutRayTheta hp (shiftBackProjectiveCut c d) i j =
      cutRayTheta hp c i j + d := by
  have htheta0 := rayThetaAt_nonneg hp i j
  have hthetapi := rayThetaAt_lt_pi hp i j
  unfold shiftBackProjectiveCut
  by_cases hdc : d ≤ c
  · rw [if_pos hdc]
    by_cases htc : rayThetaAt hp i j < c
    · have hts : rayThetaAt hp i j < c - d := by
        by_contra hnot
        have hge : c - d ≤ rayThetaAt hp i j :=
          le_of_not_gt hnot
        unfold cutRayTheta at hgap
        rw [if_pos htc] at hgap
        linarith
      unfold cutRayTheta
      rw [if_pos hts, if_pos htc]
      ring
    · have hct : c ≤ rayThetaAt hp i j :=
        le_of_not_gt htc
      have hnotS : ¬ rayThetaAt hp i j < c - d := by
        linarith
      unfold cutRayTheta
      rw [if_neg hnotS, if_neg htc]
      ring
  · have hcd : c < d := lt_of_not_ge hdc
    rw [if_neg hdc]
    by_cases htc : rayThetaAt hp i j < c
    · unfold cutRayTheta at hgap
      rw [if_pos htc] at hgap
      exfalso
      linarith
    · have hct : c ≤ rayThetaAt hp i j :=
        le_of_not_gt htc
      by_cases hts :
          rayThetaAt hp i j < c + Real.pi - d
      · unfold cutRayTheta
        rw [if_pos hts, if_neg htc]
        ring
      · have hst :
          c + Real.pi - d ≤ rayThetaAt hp i j :=
            le_of_not_gt hts
        unfold cutRayTheta at hgap
        rw [if_neg htc] at hgap
        exfalso
        linarith

/-- Circle-rotation formula on/above the shifted seam. -/
theorem cutRayTheta_shiftBack_of_ge
    {V : Type*} {p : V → Plane}
    (hp : Function.Injective p)
    {c d : ℝ}
    (hc0 : 0 ≤ c) (hcpi : c < Real.pi)
    (hd0 : 0 ≤ d) (hdpi : d < Real.pi)
    (i : V) (j : OtherVertex i)
    (hgap :
      Real.pi - d ≤ cutRayTheta hp c i j) :
    cutRayTheta hp (shiftBackProjectiveCut c d) i j =
      cutRayTheta hp c i j - (Real.pi - d) := by
  have htheta0 := rayThetaAt_nonneg hp i j
  have hthetapi := rayThetaAt_lt_pi hp i j
  unfold shiftBackProjectiveCut
  by_cases hdc : d ≤ c
  · rw [if_pos hdc]
    by_cases htc : rayThetaAt hp i j < c
    · have hst : c - d ≤ rayThetaAt hp i j := by
        unfold cutRayTheta at hgap
        rw [if_pos htc] at hgap
        linarith
      have hnotS : ¬ rayThetaAt hp i j < c - d :=
        not_lt.mpr hst
      unfold cutRayTheta
      rw [if_neg hnotS, if_pos htc]
      ring
    · unfold cutRayTheta at hgap
      rw [if_neg htc] at hgap
      exfalso
      linarith
  · have hcd : c < d := lt_of_not_ge hdc
    rw [if_neg hdc]
    by_cases htc : rayThetaAt hp i j < c
    · have hts :
          rayThetaAt hp i j < c + Real.pi - d := by
        linarith
      unfold cutRayTheta
      rw [if_pos hts, if_pos htc]
      ring
    · have hct : c ≤ rayThetaAt hp i j :=
        le_of_not_gt htc
      have hst :
          c + Real.pi - d ≤ rayThetaAt hp i j := by
        by_contra hnot
        have hts :
            rayThetaAt hp i j < c + Real.pi - d :=
          lt_of_not_ge hnot
        unfold cutRayTheta at hgap
        rw [if_neg htc] at hgap
        linarith
      have hnotS :
          ¬ rayThetaAt hp i j < c + Real.pi - d :=
        not_lt.mpr hst
      unfold cutRayTheta
      rw [if_neg hnotS, if_neg htc]
      ring

def boundaryShortCut (t delta c : ℝ) : ℝ :=
  shiftBackProjectiveCut c (delta * Real.pi / t)

theorem boundaryShiftAngle_nonneg
    {t delta : ℝ}
    (ht : 0 < t)
    (hdelta0 : 0 ≤ delta) :
    0 ≤ delta * Real.pi / t := by
  positivity

theorem boundaryShiftAngle_lt_pi
    {t delta : ℝ} {n : ℕ}
    (hn : 1 ≤ n)
    (ht : t = (n : ℝ) + delta)
    (hdelta0 : 0 ≤ delta) :
    delta * Real.pi / t < Real.pi := by
  have htpos : 0 < t := by
    rw [ht]
    have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  have hdt : delta < t := by
    rw [ht]
    have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  rw [div_lt_iff₀ htpos]
  nlinarith [Real.pi_pos]

theorem boundaryShortCut_nonneg
    {t delta c : ℝ} {n : ℕ}
    (hn : 1 ≤ n)
    (ht : t = (n : ℝ) + delta)
    (hdelta0 : 0 ≤ delta)
    (hc0 : 0 ≤ c) (hcpi : c < Real.pi) :
    0 ≤ boundaryShortCut t delta c := by
  unfold boundaryShortCut
  apply shiftBackProjectiveCut_nonneg hc0 hcpi
  · exact boundaryShiftAngle_nonneg
      (by
        rw [ht]
        have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
        linarith)
      hdelta0
  · exact boundaryShiftAngle_lt_pi hn ht hdelta0

theorem boundaryShortCut_lt_pi
    {t delta c : ℝ} {n : ℕ}
    (hn : 1 ≤ n)
    (ht : t = (n : ℝ) + delta)
    (hdelta0 : 0 ≤ delta)
    (hc0 : 0 ≤ c) (hcpi : c < Real.pi) :
    boundaryShortCut t delta c < Real.pi := by
  unfold boundaryShortCut
  apply shiftBackProjectiveCut_lt_pi hc0 hcpi
  · exact boundaryShiftAngle_nonneg
      (by
        rw [ht]
        have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
        linarith)
      hdelta0
  · exact boundaryShiftAngle_lt_pi hn ht hdelta0

theorem pi_sub_boundaryShift_eq_n_scale
    {t delta : ℝ} {n : ℕ}
    (htpos : 0 < t)
    (ht : t = (n : ℝ) + delta) :
    Real.pi - delta * Real.pi / t =
      (n : ℝ) * Real.pi / t := by
  rw [ht] at htpos ⊢
  field_simp [ne_of_gt htpos]
  ring

/-- Exact normalized rotation formula below band n. -/
theorem cutNormalizedRayTheta_boundaryShort_of_lt_n
    {V : Type*} {p : V → Plane}
    (hp : Function.Injective p)
    {t delta c : ℝ} {n : ℕ}
    (hn : 1 ≤ n)
    (htpos : 0 < t)
    (ht : t = (n : ℝ) + delta)
    (hdelta0 : 0 ≤ delta)
    (hc0 : 0 ≤ c) (hcpi : c < Real.pi)
    (i : V) (j : OtherVertex i)
    (hx :
      cutNormalizedRayTheta hp t c i j < (n : ℝ)) :
    cutNormalizedRayTheta hp t
        (boundaryShortCut t delta c) i j =
      cutNormalizedRayTheta hp t c i j + delta := by
  let d := delta * Real.pi / t
  have hd0 : 0 ≤ d :=
    boundaryShiftAngle_nonneg htpos hdelta0
  have hdpi : d < Real.pi :=
    boundaryShiftAngle_lt_pi hn ht hdelta0
  have hthreshold :
      cutRayTheta hp c i j < Real.pi - d := by
    unfold cutNormalizedRayTheta at hx
    have hscale :
        (n : ℝ) =
          t * (Real.pi - d) / Real.pi := by
      rw [pi_sub_boundaryShift_eq_n_scale htpos ht]
      field_simp [Real.pi_ne_zero]
      ring
    rw [hscale] at hx
    have hcoef : 0 < t / Real.pi := div_pos htpos Real.pi_pos
    have hrewrite :
        t * cutRayTheta hp c i j / Real.pi =
          (t / Real.pi) * cutRayTheta hp c i j := by ring
    have hrewrite2 :
        t * (Real.pi - d) / Real.pi =
          (t / Real.pi) * (Real.pi - d) := by ring
    rw [hrewrite, hrewrite2] at hx
    exact (mul_lt_mul_left hcoef).mp hx
  have htheta :=
    cutRayTheta_shiftBack_of_lt
      hp hc0 hcpi hd0 hdpi i j hthreshold
  unfold boundaryShortCut cutNormalizedRayTheta
  rw [htheta]
  dsimp [d]
  field_simp [Real.pi_ne_zero, ne_of_gt htpos]
  ring

/-- Exact normalized rotation formula on/above band n. -/
theorem cutNormalizedRayTheta_boundaryShort_of_ge_n
    {V : Type*} {p : V → Plane}
    (hp : Function.Injective p)
    {t delta c : ℝ} {n : ℕ}
    (hn : 1 ≤ n)
    (htpos : 0 < t)
    (ht : t = (n : ℝ) + delta)
    (hdelta0 : 0 ≤ delta)
    (hc0 : 0 ≤ c) (hcpi : c < Real.pi)
    (i : V) (j : OtherVertex i)
    (hx :
      (n : ℝ) ≤ cutNormalizedRayTheta hp t c i j) :
    cutNormalizedRayTheta hp t
        (boundaryShortCut t delta c) i j =
      cutNormalizedRayTheta hp t c i j - n := by
  let d := delta * Real.pi / t
  have hd0 : 0 ≤ d :=
    boundaryShiftAngle_nonneg htpos hdelta0
  have hdpi : d < Real.pi :=
    boundaryShiftAngle_lt_pi hn ht hdelta0
  have hthreshold :
      Real.pi - d ≤ cutRayTheta hp c i j := by
    unfold cutNormalizedRayTheta at hx
    have hscale :
        (n : ℝ) =
          t * (Real.pi - d) / Real.pi := by
      rw [pi_sub_boundaryShift_eq_n_scale htpos ht]
      field_simp [Real.pi_ne_zero]
      ring
    rw [hscale] at hx
    have hcoef : 0 < t / Real.pi := div_pos htpos Real.pi_pos
    have hrewrite :
        t * cutRayTheta hp c i j / Real.pi =
          (t / Real.pi) * cutRayTheta hp c i j := by ring
    have hrewrite2 :
        t * (Real.pi - d) / Real.pi =
          (t / Real.pi) * (Real.pi - d) := by ring
    rw [hrewrite, hrewrite2] at hx
    exact (mul_le_mul_left hcoef).mp hx
  have htheta :=
    cutRayTheta_shiftBack_of_ge
      hp hc0 hcpi hd0 hdpi i j hthreshold
  unfold boundaryShortCut cutNormalizedRayTheta
  rw [htheta]
  dsimp [d]
  rw [pi_sub_boundaryShift_eq_n_scale htpos ht]
  field_simp [Real.pi_ne_zero, ne_of_gt htpos]
  ring

/-- Old band 0 is contained in the short boundary arc after shifting the cut. -/
theorem boundaryShort_mem_of_band_zero
    {V : Type*} {p : V → Plane}
    (hp : Function.Injective p)
    {t delta c : ℝ} {n : ℕ}
    (hn : 1 ≤ n)
    (htpos : 0 < t)
    (ht : t = (n : ℝ) + delta)
    (hdelta0 : 0 ≤ delta)
    (hc0 : 0 ≤ c) (hcpi : c < Real.pi)
    (i : V) (j : OtherVertex i)
    (hband :
      0 ≤ cutNormalizedRayTheta hp t c i j ∧
      cutNormalizedRayTheta hp t c i j < 1) :
    0 ≤ cutNormalizedRayTheta hp t
          (boundaryShortCut t delta c) i j ∧
      cutNormalizedRayTheta hp t
          (boundaryShortCut t delta c) i j ≤ 1 + delta := by
  have hxN :
      cutNormalizedRayTheta hp t c i j < (n : ℝ) := by
    have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  rw [cutNormalizedRayTheta_boundaryShort_of_lt_n
      hp hn htpos ht hdelta0 hc0 hcpi i j hxN]
  constructor <;> linarith

/-- Old band n is contained in the same short boundary arc. -/
theorem boundaryShort_mem_of_band_last
    {V : Type*} {p : V → Plane}
    (hp : Function.Injective p)
    {t delta c : ℝ} {n : ℕ}
    (hn : 1 ≤ n)
    (htpos : 0 < t)
    (ht : t = (n : ℝ) + delta)
    (hdelta0 : 0 ≤ delta)
    (hc0 : 0 ≤ c) (hcpi : c < Real.pi)
    (i : V) (j : OtherVertex i)
    (hband :
      (n : ℝ) ≤ cutNormalizedRayTheta hp t c i j ∧
      cutNormalizedRayTheta hp t c i j < (n : ℝ) + 1) :
    0 ≤ cutNormalizedRayTheta hp t
          (boundaryShortCut t delta c) i j ∧
      cutNormalizedRayTheta hp t
          (boundaryShortCut t delta c) i j ≤ 1 + delta := by
  rw [cutNormalizedRayTheta_boundaryShort_of_ge_n
      hp hn htpos ht hdelta0 hc0 hcpi i j hband.1]
  have hxt :
      cutNormalizedRayTheta hp t c i j < t :=
    cutNormalizedRayTheta_lt_t hp htpos hc0 hcpi i j
  rw [ht] at hxt
  constructor <;> linarith

/-- The short-cut phase equals the partition-cut phase, possibly plus one full
period. -/
theorem boundaryShort_phase_eq_or_add_period
    {t delta c : ℝ} {n : ℕ}
    (hn : 1 ≤ n)
    (htpos : 0 < t)
    (ht : t = (n : ℝ) + delta)
    (hdelta0 : 0 ≤ delta)
    (hc0 : 0 ≤ c) (hcpi : c < Real.pi) :
    t * boundaryShortCut t delta c / Real.pi + delta =
        t * c / Real.pi
      ∨
    t * boundaryShortCut t delta c / Real.pi + delta =
        t * c / Real.pi + t := by
  let d := delta * Real.pi / t
  have hd0 : 0 ≤ d :=
    boundaryShiftAngle_nonneg htpos hdelta0
  have hdpi : d < Real.pi :=
    boundaryShiftAngle_lt_pi hn ht hdelta0
  unfold boundaryShortCut shiftBackProjectiveCut
  by_cases hdc : d ≤ c
  · rw [if_pos hdc]
    left
    dsimp [d]
    field_simp [Real.pi_ne_zero, ne_of_gt htpos]
    ring
  · rw [if_neg hdc]
    right
    dsimp [d]
    field_simp [Real.pi_ne_zero, ne_of_gt htpos]
    ring

/-- Cyclic critical badness is invariant when the queried phase is translated
by one full period. -/
theorem globalCyclicCriticalUnitBadAt_sub_period
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane} {hp : Function.Injective p}
    (C : ∀ i : V, CentreProjectiveCycle hp i)
    {t delta : ℝ}
    (u : GlobalUnitGapSlot C t)
    (x : ℝ)
    (hbad :
      GlobalCyclicCriticalUnitBadAt C t delta u (x + t)) :
    GlobalCyclicCriticalUnitBadAt C t delta u x := by
  rcases hbad with ⟨k, s, hs1, hsTop, hxL, hxR⟩
  refine ⟨k - 1, s, hs1, hsTop, ?_, ?_⟩
  · unfold criticalBadLeft at hxL ⊢
    push_cast
    nlinarith
  · unfold criticalBadRight at hxR ⊢
    push_cast
    nlinarith

#print axioms cutRayTheta_shiftBack_of_lt
#print axioms cutRayTheta_shiftBack_of_ge
#print axioms cutNormalizedRayTheta_boundaryShort_of_lt_n
#print axioms cutNormalizedRayTheta_boundaryShort_of_ge_n
#print axioms boundaryShort_mem_of_band_zero
#print axioms boundaryShort_mem_of_band_last
#print axioms boundaryShort_phase_eq_or_add_period
#print axioms globalCyclicCriticalUnitBadAt_sub_period

end JSP000404Research
