
import JSP000404Research.CyclicProjectiveGaps
import JSP000404Research.PinnedCyclicDeletionGain
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Tactic

/-!
# One-dimensional unit-band capacity for a sorted cyclic direction list

Let

  0 <= x_0 <= ... <= x_m < t < n+1.

The occupied unit bands are the distinct natural floors floor(x_i).

The cyclic direction gaps are

  x_{i+1}-x_i

together with the wrap gap

  t + x_0 - x_m.

Take the natural floor of every gap and apply the Sendov list exponent

  sum max(floor(gap)-1,0).

Every exponent unit corresponds to a whole unit band skipped between two
successive occupied bands, including the cyclic wrap.  Hence

  occupiedBandCount + cyclicGapExponent <= n+1.

This is the exact one-dimensional inequality needed to compare the canonical
Sendov centre exponent with the full (n+1)-band ordered colouring once the two
projective cuts are identified.
-/

namespace JSP000404Research

open Real

def occupiedNatBands (xs : List ℝ) : Finset ℕ :=
  (xs.map Nat.floor).toFinset

def linearCyclicGapQuotients (t : ℝ) : List ℝ → List ℕ
  | [] => []
  | a :: xs =>
      (successiveDiffsFrom a xs).map Nat.floor ++
        [Nat.floor (a + t - xs.getLastD a)]

@[simp] theorem occupiedNatBands_nil :
    occupiedNatBands [] = ∅ := by
  simp [occupiedNatBands]

@[simp] theorem occupiedNatBands_cons
    (a : ℝ) (xs : List ℝ) :
    occupiedNatBands (a :: xs) =
      insert (Nat.floor a) (occupiedNatBands xs) := by
  simp [occupiedNatBands]

theorem natFloor_sub_le_floor_sub
    {a b : ℝ}
    (ha0 : 0 ≤ a)
    (hab : a ≤ b) :
    Nat.floor (b - a) ≤ Nat.floor b - Nat.floor a := by
  have hb0 : 0 ≤ b := ha0.trans hab
  have hAB :
      Nat.floor a ≤ Nat.floor b :=
    Nat.floor_mono hab
  have hdiff0 : 0 ≤ b - a := sub_nonneg.mpr hab
  have hfa :
      ((Nat.floor a : ℕ) : ℝ) ≤ a :=
    Nat.floor_le ha0
  have hfb :
      b < ((Nat.floor b : ℕ) : ℝ) + 1 :=
    Nat.lt_floor_add_one b
  have hlt :
      b - a <
        (((Nat.floor b - Nat.floor a : ℕ) : ℝ) + 1) := by
    rw [Nat.cast_sub hAB]
    push_cast
    linarith
  have hfloorlt :
      Nat.floor (b - a) <
        (Nat.floor b - Nat.floor a) + 1 :=
    (Nat.floor_lt hdiff0).2 (by
      norm_num at hlt ⊢
      exact hlt)
  omega

theorem excess_natFloor_sub_add_one_le_floor_sub_of_floor_lt
    {a b : ℝ}
    (ha0 : 0 ≤ a)
    (hab : a ≤ b)
    (hfloor :
      Nat.floor a < Nat.floor b) :
    excess (Nat.floor (b - a)) + 1 ≤
      Nat.floor b - Nat.floor a := by
  have hq :=
    natFloor_sub_le_floor_sub ha0 hab
  unfold excess
  omega

theorem natFloor_sub_eq_zero_of_floor_eq
    {a b : ℝ}
    (ha0 : 0 ≤ a)
    (hab : a ≤ b)
    (hfloor :
      Nat.floor a = Nat.floor b) :
    Nat.floor (b - a) = 0 := by
  have hq :=
    natFloor_sub_le_floor_sub ha0 hab
  rw [hfloor] at hq
  simp at hq
  exact Nat.eq_zero_of_le_zero hq

theorem head_floor_le_of_mem_sorted
    {a x : ℝ} {xs : List ℝ}
    (hsorted : (a :: xs).Pairwise (· ≤ ·))
    (hx : x ∈ a :: xs) :
    Nat.floor a ≤ Nat.floor x := by
  simp only [List.mem_cons] at hx
  rcases hx with rfl | hx
  · exact le_rfl
  · have hax :
        a ≤ x :=
      (List.pairwise_cons.mp hsorted).1 x hx
    exact Nat.floor_mono hax

theorem head_le_getLastD_of_pairwise
    (a : ℝ) (xs : List ℝ)
    (hsorted : (a :: xs).Pairwise (· ≤ ·)) :
    a ≤ xs.getLastD a := by
  cases xs with
  | nil =>
      simp
  | cons b bs =>
      have hmem :
          (b :: bs).getLastD a ∈ a :: b :: bs := by
        exact List.getLastD_mem_cons a (b :: bs)
      exact
        (List.pairwise_cons.mp hsorted).1
          ((b :: bs).getLastD a)
          (by simpa using hmem)

theorem floor_head_le_floor_getLastD_of_pairwise
    (a : ℝ) (xs : List ℝ)
    (hsorted : (a :: xs).Pairwise (· ≤ ·)) :
    Nat.floor a ≤ Nat.floor (xs.getLastD a) :=
  Nat.floor_mono
    (head_le_getLastD_of_pairwise a xs hsorted)

/-- Interior gap exponent plus the number of occupied floor bands is bounded
by the integer span from the first occupied band to the last. -/
theorem interior_gapExponent_add_occupied_le_span
    (a : ℝ) (xs : List ℝ)
    (ha0 : 0 ≤ a)
    (hsorted : (a :: xs).Pairwise (· ≤ ·)) :
    listExponent ((successiveDiffsFrom a xs).map Nat.floor) +
        (occupiedNatBands (a :: xs)).card
      ≤
    Nat.floor (xs.getLastD a) - Nat.floor a + 1 := by
  induction xs generalizing a with
  | nil =>
      simp [successiveDiffsFrom, occupiedNatBands, listExponent]
  | cons b bs ih =>
      have hpair := List.pairwise_cons.mp hsorted
      have hab : a ≤ b := hpair.1 b (by simp)
      have hb0 : 0 ≤ b := ha0.trans hab
      have htail :
          (b :: bs).Pairwise (· ≤ ·) :=
        hpair.2
      have hih :=
        ih b hb0 htail
      have hAB :
          Nat.floor a ≤ Nat.floor b :=
        Nat.floor_mono hab
      by_cases hEq :
          Nat.floor a = Nat.floor b
      · have hq0 :
            Nat.floor (b - a) = 0 :=
          natFloor_sub_eq_zero_of_floor_eq
            ha0 hab hEq
        have hbands :
            occupiedNatBands (a :: b :: bs) =
              occupiedNatBands (b :: bs) := by
          simp [occupiedNatBands, hEq]
        rw [hbands]
        simp only [successiveDiffsFrom, List.map_cons,
          listExponent, List.map_cons, List.sum_cons]
        rw [hq0]
        simp [excess, hEq] at hih ⊢
        exact hih
      · have hLt :
            Nat.floor a < Nat.floor b := by
          omega
        have hnotmem :
            Nat.floor a ∉ occupiedNatBands (b :: bs) := by
          intro hmem
          rw [occupiedNatBands, List.mem_toFinset,
            List.mem_map] at hmem
          obtain ⟨x, hx, hxFloor⟩ := hmem
          have hBx :
              Nat.floor b ≤ Nat.floor x :=
            head_floor_le_of_mem_sorted
              htail hx
          rw [← hxFloor] at hBx
          omega
        have hbands :
            (occupiedNatBands (a :: b :: bs)).card =
              (occupiedNatBands (b :: bs)).card + 1 := by
          rw [occupiedNatBands_cons,
              Finset.card_insert_of_not_mem hnotmem]
          omega
        have hgap :
            excess (Nat.floor (b - a)) + 1 ≤
              Nat.floor b - Nat.floor a :=
          excess_natFloor_sub_add_one_le_floor_sub_of_floor_lt
            ha0 hab hLt
        have hBLast :
            Nat.floor b ≤
              Nat.floor (bs.getLastD b) :=
          floor_head_le_floor_getLastD_of_pairwise
            b bs htail
        simp only [successiveDiffsFrom, List.map_cons,
          listExponent, List.map_cons, List.sum_cons]
        rw [hbands]
        change
          excess (Nat.floor (b - a)) +
              listExponent
                ((successiveDiffsFrom b bs).map Nat.floor) +
              ((occupiedNatBands (b :: bs)).card + 1)
            ≤
          Nat.floor (bs.getLastD b) - Nat.floor a + 1
        omega

/-- The wrap-gap exponent is bounded by the number of unit bands outside the
integer span of the first and last occupied bands. -/
theorem wrap_gap_excess_le_outer_empty_band_count
    {a z t : ℝ} {n : ℕ}
    (ha0 : 0 ≤ a)
    (haz : a ≤ z)
    (hzt : z < t)
    (ht : t < (n : ℝ) + 1) :
    excess (Nat.floor (a + t - z)) ≤
      n - Nat.floor z + Nat.floor a := by
  have hz0 : 0 ≤ z := ha0.trans haz
  have hAz :
      Nat.floor a ≤ Nat.floor z :=
    Nat.floor_mono haz
  have hzN :
      Nat.floor z ≤ n := by
    have hzn1 :
        z < ((n + 1 : ℕ) : ℝ) := by
      push_cast
      linarith
    have hf :
        Nat.floor z < n + 1 :=
      (Nat.floor_lt hz0).2 hzn1
    omega
  have hwrap0 :
      0 ≤ a + t - z := by
    linarith
  have hfa :
      a < ((Nat.floor a : ℕ) : ℝ) + 1 :=
    Nat.lt_floor_add_one a
  have hfz :
      ((Nat.floor z : ℕ) : ℝ) ≤ z :=
    Nat.floor_le hz0
  have hreal :
      a + t - z <
        (((n - Nat.floor z + Nat.floor a + 1 : ℕ) : ℝ) + 1) := by
    rw [Nat.cast_add, Nat.cast_add, Nat.cast_one,
        Nat.cast_sub hzN]
    push_cast
    linarith
  have hq :
      Nat.floor (a + t - z) ≤
        n - Nat.floor z + Nat.floor a + 1 := by
    have hlt :
        Nat.floor (a + t - z) <
          (n - Nat.floor z + Nat.floor a + 1) + 1 :=
      (Nat.floor_lt hwrap0).2 (by
        norm_num at hreal ⊢
        exact hreal)
    omega
  unfold excess
  omega

/-- Main one-dimensional full-band inequality. -/
theorem linear_cyclic_gapExponent_add_occupied_le
    {t : ℝ} {n : ℕ}
    (a : ℝ) (xs : List ℝ)
    (ha0 : 0 ≤ a)
    (hsorted : (a :: xs).Pairwise (· ≤ ·))
    (hall : ∀ x ∈ a :: xs, x < t)
    (ht : t < (n : ℝ) + 1) :
    listExponent (linearCyclicGapQuotients t (a :: xs)) +
        (occupiedNatBands (a :: xs)).card
      ≤
    n + 1 := by
  have hlast :
      xs.getLastD a < t :=
    hall _ (List.getLastD_mem_cons a xs)
  have haz :
      a ≤ xs.getLastD a :=
    head_le_getLastD_of_pairwise a xs hsorted
  have hinterior :=
    interior_gapExponent_add_occupied_le_span
      a xs ha0 hsorted
  have hwrap :=
    wrap_gap_excess_le_outer_empty_band_count
      ha0 haz hlast ht
  have hfloorAZ :=
    floor_head_le_floor_getLastD_of_pairwise
      a xs hsorted
  have hlast0 : 0 ≤ xs.getLastD a :=
    ha0.trans haz
  have hlastN :
      Nat.floor (xs.getLastD a) ≤ n := by
    have hlt :
        xs.getLastD a < ((n + 1 : ℕ) : ℝ) := by
      push_cast
      linarith
    have hf :
        Nat.floor (xs.getLastD a) < n + 1 :=
      (Nat.floor_lt hlast0).2 hlt
    omega
  simp only [linearCyclicGapQuotients,
    listExponent_append, listExponent_singleton]
  change
    listExponent ((successiveDiffsFrom a xs).map Nat.floor) +
        excess (Nat.floor (a + t - xs.getLastD a)) +
        (occupiedNatBands (a :: xs)).card
      ≤ n + 1
  omega

#print axioms natFloor_sub_le_floor_sub
#print axioms interior_gapExponent_add_occupied_le_span
#print axioms wrap_gap_excess_le_outer_empty_band_count
#print axioms linear_cyclic_gapExponent_add_occupied_le

end JSP000404Research
