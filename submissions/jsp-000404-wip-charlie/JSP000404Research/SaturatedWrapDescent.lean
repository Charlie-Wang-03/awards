import JSP000404Research.LinearBandGapStepTight
import Mathlib.Tactic

/-!
# Fractional descent forced by a positive first band in a saturated cycle

Let a::xs be a sorted local value list in [0,t), with t=n+delta and last
occupied floor n.  In a saturated equality case the cyclic wrap contribution
satisfies

  excess(floor(a+t-last)) = floor(a).

If floor(a)>0, then the wrap floor must be floor(a)+1.  Since last>=n and
t=n+delta, this forces the fractional part of a to be at least 1-delta.

In the lower branch delta<1/2, the first fractional part is therefore >1/2.
Every top-band value is <n+delta, so the final fractional part is <delta<1/2.

Thus the fractional part strictly drops somewhere along the sorted list.
Stepwise interior tightness implies that such a drop cannot occur inside one
band, nor across a jump of two or more bands.  It must pass through an
adjacent unit-band step.

The recursive predicate NoUnitBandStep records absence of such steps.
-/

namespace JSP000404Research

def floorRemainder (x : ℝ) : ℝ :=
  x - (Nat.floor x : ℝ)

def NoUnitBandStep : ℝ → List ℝ → Prop
  | _, [] => True
  | a, b :: bs =>
      Nat.floor b ≠ Nat.floor a + 1 ∧
      NoUnitBandStep b bs

@[simp] theorem noUnitBandStep_nil
    (a : ℝ) :
    NoUnitBandStep a [] := by
  rfl

@[simp] theorem noUnitBandStep_cons
    (a b : ℝ) (bs : List ℝ) :
    NoUnitBandStep a (b :: bs) ↔
      Nat.floor b ≠ Nat.floor a + 1 ∧
      NoUnitBandStep b bs := by
  rfl

theorem floor_wrap_eq_first_add_one_of_positive_excess
    {q f : ℕ}
    (hf : 1 ≤ f)
    (h : excess q = f) :
    q = f + 1 := by
  unfold excess at h
  omega

/-- Positive first occupied band plus saturated wrap equality puts the first
value in the upper part of its unit band. -/
theorem saturated_wrap_first_remainder_gt_half
    {a z t delta : ℝ} {n : ℕ}
    (ha0 : 0 ≤ a)
    (haz : a ≤ z)
    (hzlt : z < t)
    (ht : t = (n : ℝ) + delta)
    (hzFloor : Nat.floor z = n)
    (hwrap :
      excess (Nat.floor (a + t - z)) =
        Nat.floor a)
    (hfirstPos : 1 ≤ Nat.floor a)
    (hdeltaHalf : delta < (1 : ℝ) / 2) :
    (Nat.floor a : ℝ) + (1 : ℝ) / 2 < a := by
  have hz0 : 0 ≤ z := ha0.trans haz
  have hgap0 : 0 ≤ a + t - z := by
    have : z < t := hzlt
    linarith
  have hq :
      Nat.floor (a + t - z) =
        Nat.floor a + 1 :=
    floor_wrap_eq_first_add_one_of_positive_excess
      hfirstPos hwrap
  have hfloorGap :
      (Nat.floor (a + t - z) : ℝ) ≤
        a + t - z :=
    Nat.floor_le hgap0
  have hzLower :
      (n : ℝ) ≤ z := by
    have h := Nat.floor_le hz0
    rw [hzFloor] at h
    exact h
  have hqReal :
      (Nat.floor (a + t - z) : ℝ) =
        (Nat.floor a : ℝ) + 1 := by
    exact_mod_cast hq
  rw [hqReal, ht] at hfloorGap
  linarith

/-- Every final value in the top band n lies below fractional height delta. -/
theorem top_band_last_remainder_lt_delta
    {z t delta : ℝ} {n : ℕ}
    (hzlt : z < t)
    (ht : t = (n : ℝ) + delta)
    (hzFloor : Nat.floor z = n) :
    floorRemainder z < delta := by
  unfold floorRemainder
  rw [hzFloor]
  rw [ht] at hzlt
  linarith

/-- A tight adjacent step which is not a unit-band step cannot decrease the
fractional remainder. -/
theorem floorRemainder_le_of_tight_of_not_unit
    {a b : ℝ}
    (ha0 : 0 ≤ a)
    (hab : a ≤ b)
    (htight :
      if Nat.floor a = Nat.floor b then
        Nat.floor (b - a) = 0
      else
        excess (Nat.floor (b - a)) + 1 =
          Nat.floor b - Nat.floor a)
    (hnotUnit :
      Nat.floor b ≠ Nat.floor a + 1) :
    floorRemainder a ≤ floorRemainder b := by
  have hfloorLe :
      Nat.floor a ≤ Nat.floor b :=
    Nat.floor_mono hab
  by_cases heq : Nat.floor a = Nat.floor b
  · unfold floorRemainder
    rw [heq]
    linarith
  · have hlt :
        Nat.floor a < Nat.floor b := by
      omega
    have hjump :
        2 ≤ Nat.floor b - Nat.floor a := by
      omega
    have htight' :
        excess (Nat.floor (b - a)) + 1 =
          Nat.floor b - Nat.floor a := by
      simpa [heq] using htight
    have hgapFloor :=
      floor_gap_eq_floor_jump_of_tight_of_two_le
        ha0 hab htight' hjump
    have hgap0 : 0 ≤ b - a := sub_nonneg.mpr hab
    have hfloorGap :
        (Nat.floor (b - a) : ℝ) ≤ b - a :=
      Nat.floor_le hgap0
    have hcast :
        ((Nat.floor b - Nat.floor a : ℕ) : ℝ) =
          (Nat.floor b : ℝ) - (Nat.floor a : ℝ) := by
      rw [Nat.cast_sub hfloorLe]
    rw [hgapFloor, hcast] at hfloorGap
    unfold floorRemainder
    linarith

/-- If every tight adjacent step avoids a unit band increment, fractional
remainders are nondecreasing from the first to the final value. -/
theorem floorRemainder_head_le_last_of_tight_noUnit
    (a : ℝ) (xs : List ℝ)
    (ha0 : 0 ≤ a)
    (hsorted : (a :: xs).Pairwise (· ≤ ·))
    (htight : InteriorBandGapTight a xs)
    (hnoUnit : NoUnitBandStep a xs) :
    floorRemainder a ≤
      floorRemainder (xs.getLastD a) := by
  induction xs generalizing a with
  | nil =>
      simp [floorRemainder]
  | cons b bs ih =>
      have hp := List.pairwise_cons.mp hsorted
      have hab : a ≤ b :=
        hp.1 b (by simp)
      have hb0 : 0 ≤ b := ha0.trans hab
      have htail :
          (b :: bs).Pairwise (· ≤ ·) :=
        hp.2
      have htightHead := (interiorBandGapTight_cons a b bs).1 htight
      have hnoHead := (noUnitBandStep_cons a b bs).1 hnoUnit
      have hlocal :
          floorRemainder a ≤ floorRemainder b :=
        floorRemainder_le_of_tight_of_not_unit
          ha0 hab htightHead.1 hnoHead.1
      have hrec :
          floorRemainder b ≤
            floorRemainder (bs.getLastD b) :=
        ih b hb0 htail htightHead.2 hnoHead.2
      simpa [List.getLastD_cons] using hlocal.trans hrec

/-- A strict drop of fractional remainder in a stepwise-tight list forces at
least one adjacent unit-band step. -/
theorem not_noUnitBandStep_of_fractional_drop
    (a : ℝ) (xs : List ℝ)
    (ha0 : 0 ≤ a)
    (hsorted : (a :: xs).Pairwise (· ≤ ·))
    (htight : InteriorBandGapTight a xs)
    (hdrop :
      floorRemainder (xs.getLastD a) <
        floorRemainder a) :
    ¬ NoUnitBandStep a xs := by
  intro hno
  have hmono :=
    floorRemainder_head_le_last_of_tight_noUnit
      a xs ha0 hsorted htight hno
  linarith

/-- Saturated lower-branch wrap equality with a positive first occupied band
forces an adjacent unit-band step somewhere in the tight interior profile. -/
theorem saturated_wrap_positive_first_forces_unit_step
    {a t delta : ℝ} {n : ℕ}
    (xs : List ℝ)
    (ha0 : 0 ≤ a)
    (hsorted : (a :: xs).Pairwise (· ≤ ·))
    (hall : ∀ x ∈ a :: xs, x < t)
    (ht : t = (n : ℝ) + delta)
    (hzFloor : Nat.floor (xs.getLastD a) = n)
    (hwrap :
      excess (Nat.floor (a + t - xs.getLastD a)) =
        Nat.floor a)
    (hfirstPos : 1 ≤ Nat.floor a)
    (hdeltaHalf : delta < (1 : ℝ) / 2)
    (htight : InteriorBandGapTight a xs) :
    ¬ NoUnitBandStep a xs := by
  have haz :
      a ≤ xs.getLastD a :=
    head_le_getLastD_of_pairwise a xs hsorted
  have hzlt :
      xs.getLastD a < t :=
    hall _ (List.getLastD_mem_cons a xs)
  have hfirstHigh :=
    saturated_wrap_first_remainder_gt_half
      ha0 haz hzlt ht hzFloor hwrap
      hfirstPos hdeltaHalf
  have hlastLow :=
    top_band_last_remainder_lt_delta
      hzlt ht hzFloor
  have hdelta :
      delta < (1 : ℝ) / 2 :=
    hdeltaHalf
  have hdrop :
      floorRemainder (xs.getLastD a) <
        floorRemainder a := by
    unfold floorRemainder at hfirstHigh
    have hfirstRem :
        (1 : ℝ) / 2 < floorRemainder a := by
      unfold floorRemainder
      linarith [hfirstHigh]
    linarith
  exact not_noUnitBandStep_of_fractional_drop
    a xs ha0 hsorted htight hdrop


def HasZeroQuotientUnitStep : ℝ → List ℝ → Prop
  | _, [] => False
  | a, b :: bs =>
      (Nat.floor b = Nat.floor a + 1 ∧
        Nat.floor (b - a) = 0)
      ∨
      HasZeroQuotientUnitStep b bs

@[simp] theorem hasZeroQuotientUnitStep_nil
    (a : ℝ) :
    ¬ HasZeroQuotientUnitStep a [] := by
  simp [HasZeroQuotientUnitStep]

@[simp] theorem hasZeroQuotientUnitStep_cons
    (a b : ℝ) (bs : List ℝ) :
    HasZeroQuotientUnitStep a (b :: bs) ↔
      (Nat.floor b = Nat.floor a + 1 ∧
        Nat.floor (b - a) = 0)
      ∨
      HasZeroQuotientUnitStep b bs := by
  rfl

/-- If a tight adjacent step is not a zero-quotient unit-band crossing, its
fractional remainder cannot decrease. -/
theorem floorRemainder_le_of_tight_of_not_zeroUnit
    {a b : ℝ}
    (ha0 : 0 ≤ a)
    (hab : a ≤ b)
    (htight :
      if Nat.floor a = Nat.floor b then
        Nat.floor (b - a) = 0
      else
        excess (Nat.floor (b - a)) + 1 =
          Nat.floor b - Nat.floor a)
    (hnot :
      ¬ (Nat.floor b = Nat.floor a + 1 ∧
        Nat.floor (b - a) = 0)) :
    floorRemainder a ≤ floorRemainder b := by
  have hfloorLe :
      Nat.floor a ≤ Nat.floor b :=
    Nat.floor_mono hab
  by_cases heq : Nat.floor a = Nat.floor b
  · unfold floorRemainder
    rw [heq]
    linarith
  · have hlt :
        Nat.floor a < Nat.floor b := by
      omega
    by_cases hunit :
        Nat.floor b = Nat.floor a + 1
    · have hqLe :
          Nat.floor (b - a) ≤
            Nat.floor b - Nat.floor a :=
        natFloor_sub_le_floor_sub ha0 hab
      have hqNe : Nat.floor (b - a) ≠ 0 := by
        intro hq0
        exact hnot ⟨hunit, hq0⟩
      have hqOne :
          Nat.floor (b - a) = 1 := by
        rw [hunit] at hqLe
        omega
      have hgap0 : 0 ≤ b - a := sub_nonneg.mpr hab
      have hgapLower :
          (1 : ℝ) ≤ b - a := by
        have h :=
          Nat.floor_le hgap0
        rw [hqOne] at h
        norm_num at h ⊢
        exact h
      unfold floorRemainder
      have hunitReal :
          (Nat.floor b : ℝ) =
            (Nat.floor a : ℝ) + 1 := by
        exact_mod_cast hunit
      rw [hunitReal]
      linarith
    · have hjump :
          2 ≤ Nat.floor b - Nat.floor a := by
        omega
      have htight' :
          excess (Nat.floor (b - a)) + 1 =
            Nat.floor b - Nat.floor a := by
        simpa [heq] using htight
      have hgapFloor :=
        floor_gap_eq_floor_jump_of_tight_of_two_le
          ha0 hab htight' hjump
      have hgap0 : 0 ≤ b - a := sub_nonneg.mpr hab
      have hfloorGap :
          (Nat.floor (b - a) : ℝ) ≤ b - a :=
        Nat.floor_le hgap0
      have hcast :
          ((Nat.floor b - Nat.floor a : ℕ) : ℝ) =
            (Nat.floor b : ℝ) - (Nat.floor a : ℝ) := by
        rw [Nat.cast_sub hfloorLe]
      rw [hgapFloor, hcast] at hfloorGap
      unfold floorRemainder
      linarith

/-- If a stepwise-tight list has no zero-quotient unit crossing, its
fractional remainders are nondecreasing from first to last. -/
theorem floorRemainder_head_le_last_of_tight_no_zeroUnit
    (a : ℝ) (xs : List ℝ)
    (ha0 : 0 ≤ a)
    (hsorted : (a :: xs).Pairwise (· ≤ ·))
    (htight : InteriorBandGapTight a xs)
    (hno : ¬ HasZeroQuotientUnitStep a xs) :
    floorRemainder a ≤
      floorRemainder (xs.getLastD a) := by
  induction xs generalizing a with
  | nil =>
      simp [floorRemainder]
  | cons b bs ih =>
      have hp := List.pairwise_cons.mp hsorted
      have hab : a ≤ b :=
        hp.1 b (by simp)
      have hb0 : 0 ≤ b := ha0.trans hab
      have htail :
          (b :: bs).Pairwise (· ≤ ·) :=
        hp.2
      have htightHead :=
        (interiorBandGapTight_cons a b bs).1 htight
      have hnoHead :
          ¬ (Nat.floor b = Nat.floor a + 1 ∧
              Nat.floor (b - a) = 0) := by
        intro hbad
        apply hno
        rw [hasZeroQuotientUnitStep_cons]
        exact Or.inl hbad
      have hnoTail :
          ¬ HasZeroQuotientUnitStep b bs := by
        intro hbad
        apply hno
        rw [hasZeroQuotientUnitStep_cons]
        exact Or.inr hbad
      have hlocal :
          floorRemainder a ≤ floorRemainder b :=
        floorRemainder_le_of_tight_of_not_zeroUnit
          ha0 hab htightHead.1 hnoHead
      have hrec :
          floorRemainder b ≤
            floorRemainder (bs.getLastD b) :=
        ih b hb0 htail htightHead.2 hnoTail
      simpa [List.getLastD_cons] using hlocal.trans hrec

/-- Strict overall fractional descent forces a zero-quotient unit-band
crossing somewhere in a stepwise-tight list. -/
theorem hasZeroQuotientUnitStep_of_fractional_drop
    (a : ℝ) (xs : List ℝ)
    (ha0 : 0 ≤ a)
    (hsorted : (a :: xs).Pairwise (· ≤ ·))
    (htight : InteriorBandGapTight a xs)
    (hdrop :
      floorRemainder (xs.getLastD a) <
        floorRemainder a) :
    HasZeroQuotientUnitStep a xs := by
  by_contra hno
  have hmono :=
    floorRemainder_head_le_last_of_tight_no_zeroUnit
      a xs ha0 hsorted htight hno
  linarith

/-- Sharp form of the lower-branch saturated descent: a positive first band
forces an actual zero-quotient gap crossing one unit-band boundary. -/
theorem saturated_wrap_positive_first_has_zeroUnitStep
    {a t delta : ℝ} {n : ℕ}
    (xs : List ℝ)
    (ha0 : 0 ≤ a)
    (hsorted : (a :: xs).Pairwise (· ≤ ·))
    (hall : ∀ x ∈ a :: xs, x < t)
    (ht : t = (n : ℝ) + delta)
    (hzFloor : Nat.floor (xs.getLastD a) = n)
    (hwrap :
      excess (Nat.floor (a + t - xs.getLastD a)) =
        Nat.floor a)
    (hfirstPos : 1 ≤ Nat.floor a)
    (hdeltaHalf : delta < (1 : ℝ) / 2)
    (htight : InteriorBandGapTight a xs) :
    HasZeroQuotientUnitStep a xs := by
  have haz :
      a ≤ xs.getLastD a :=
    head_le_getLastD_of_pairwise a xs hsorted
  have hzlt :
      xs.getLastD a < t :=
    hall _ (List.getLastD_mem_cons a xs)
  have hfirstHigh :=
    saturated_wrap_first_remainder_gt_half
      ha0 haz hzlt ht hzFloor hwrap
      hfirstPos hdeltaHalf
  have hlastLow :=
    top_band_last_remainder_lt_delta
      hzlt ht hzFloor
  have hfirstRem :
      (1 : ℝ) / 2 < floorRemainder a := by
    unfold floorRemainder
    linarith [hfirstHigh]
  have hdrop :
      floorRemainder (xs.getLastD a) <
        floorRemainder a := by
    linarith
  exact hasZeroQuotientUnitStep_of_fractional_drop
    a xs ha0 hsorted htight hdrop

#print axioms saturated_wrap_first_remainder_gt_half
#print axioms floorRemainder_le_of_tight_of_not_unit
#print axioms floorRemainder_head_le_last_of_tight_noUnit
#print axioms saturated_wrap_positive_first_forces_unit_step

end JSP000404Research
