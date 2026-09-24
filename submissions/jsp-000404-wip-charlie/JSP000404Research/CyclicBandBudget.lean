
import JSP000404Research.CyclicProjectiveGaps
import JSP000404Research.PinnedCyclicDeletionGain
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Data.List.ToFinset
import Mathlib.Tactic

/-!
# Cyclic unit-band budget for one sorted direction cycle

Let

  0 <= x_0 <= ... <= x_{m-1} < t,
  t = n + delta,
  delta < 1.

Put every x_j into its integer unit band floor(x_j).  Let q be the natural
floor quotients of the cyclic real gaps

  x_{j+1}-x_j,
  x_0+t-x_{m-1}.

Then

  listExponent(q) + number_of_occupied_unit_bands <= n+1.

The proof is local and exact.

For an ordinary adjacent pair, the excess floor quotient is at most the number
of integer bands skipped strictly between the two occupied bands.

For the wrap gap, its excess is at most the number of bands skipped around the
top boundary.

For a nondecreasing list of integer band indices, all skipped-band intervals
are disjoint and their total cardinality is exactly

  (n+1) - number_of_distinct_occupied_bands.

This is the one-dimensional arithmetic core of the desired standard
(n+1)-band estimate

  active(i) <= n - centreExponent(i) + 1.
-/

namespace JSP000404Research

open Real

def strictBandChangeCountFrom (a : ℕ) : List ℕ → ℕ
  | [] => 0
  | b :: bs =>
      (if a < b then 1 else 0) +
        strictBandChangeCountFrom b bs

def skippedBandCountFrom (a : ℕ) : List ℕ → ℕ
  | [] => 0
  | b :: bs =>
      (if a < b then b - a - 1 else 0) +
        skippedBandCountFrom b bs

/-- For a nondecreasing natural list, skipped bands plus strict band changes
telescope to last-first. -/
theorem skipped_add_changes_eq_last_sub_first
    (a : ℕ) (xs : List ℕ)
    (hsorted : (a :: xs).Pairwise (· ≤ ·)) :
    skippedBandCountFrom a xs +
        strictBandChangeCountFrom a xs
      =
    xs.getLastD a - a := by
  induction xs generalizing a with
  | nil =>
      simp [skippedBandCountFrom,
        strictBandChangeCountFrom]
  | cons b bs ih =>
      rw [List.pairwise_cons] at hsorted
      have hab : a ≤ b :=
        hsorted.1 b (by simp)
      have htail :
          (b :: bs).Pairwise (· ≤ ·) :=
        hsorted.2
      have hrec :=
        ih b htail
      by_cases hlt : a < b
      · simp [skippedBandCountFrom,
          strictBandChangeCountFrom,
          hlt, List.getLastD_cons] at *
        omega
      · have heq : a = b := by omega
        subst b
        simpa [skippedBandCountFrom,
          strictBandChangeCountFrom,
          List.getLastD_cons] using hrec

/-- On a nondecreasing nonempty list, the number of distinct entries is one
plus the number of strict changes. -/
theorem toFinset_card_eq_changes_add_one
    (a : ℕ) (xs : List ℕ)
    (hsorted : (a :: xs).Pairwise (· ≤ ·)) :
    (a :: xs).toFinset.card =
      strictBandChangeCountFrom a xs + 1 := by
  induction xs generalizing a with
  | nil =>
      simp [strictBandChangeCountFrom]
  | cons b bs ih =>
      rw [List.pairwise_cons] at hsorted
      have hab : a ≤ b :=
        hsorted.1 b (by simp)
      have htail :
          (b :: bs).Pairwise (· ≤ ·) :=
        hsorted.2
      have hrec := ih b htail
      by_cases hlt : a < b
      · have hnot :
          a ∉ b :: bs := by
          intro ha
          rcases List.mem_cons.mp ha with habEq | haBs
          · subst b
            exact (lt_irrefl a) hlt
          · have hba :
                b ≤ a :=
              (List.pairwise_cons.mp htail).1 a haBs
            exact (not_le_of_gt hlt) hba
        simp [strictBandChangeCountFrom,
          hlt, hnot, hrec]
      · have heq : a = b := by omega
        subst b
        simpa [strictBandChangeCountFrom] using hrec

/-- Exact total skipped-band count, including the cyclic wrap from last back
to first through the top band. -/
theorem total_skipped_eq_missing_bands
    (n a : ℕ) (xs : List ℕ)
    (hsorted : (a :: xs).Pairwise (· ≤ ·))
    (hbound : ∀ m ∈ a :: xs, m ≤ n) :
    skippedBandCountFrom a xs +
        (n - xs.getLastD a + a)
      =
    n + 1 - (a :: xs).toFinset.card := by
  have htel :=
    skipped_add_changes_eq_last_sub_first
      a xs hsorted
  have hcard :=
    toFinset_card_eq_changes_add_one
      a xs hsorted
  have hlastMem :
      xs.getLastD a ∈ a :: xs :=
    List.getLastD_mem_cons a xs
  have hlastN :
      xs.getLastD a ≤ n :=
    hbound _ hlastMem
  have haLast :
      a ≤ xs.getLastD a := by
    cases xs with
    | nil =>
        simp
    | cons b bs =>
        rw [List.pairwise_cons] at hsorted
        exact hsorted.1 _
          (List.getLastD_mem_cons b bs)
  omega

/-- Natural floor is monotone on nonnegative reals. -/
theorem natFloor_mono_of_nonneg
    {x y : ℝ}
    (hx0 : 0 ≤ x)
    (hxy : x ≤ y) :
    Nat.floor x ≤ Nat.floor y := by
  have hy0 : 0 ≤ y := hx0.trans hxy
  have hxLo :
      ((Nat.floor x : ℕ) : ℝ) ≤ x :=
    Nat.floor_le hx0
  have hyHi :
      y < ((Nat.floor y : ℕ) : ℝ) + 1 :=
    Nat.lt_floor_add_one y
  by_contra hnot
  have hgt :
      Nat.floor y < Nat.floor x := by
    omega
  have hcast :
      ((Nat.floor y : ℕ) : ℝ) + 1 ≤
        ((Nat.floor x : ℕ) : ℝ) := by
    exact_mod_cast hgt
  linarith

/-- The floor-band list of a nonnegative sorted real list is nondecreasing. -/
theorem floor_list_pairwise
    (a : ℝ) (xs : List ℝ)
    (hsorted : (a :: xs).Pairwise (· ≤ ·)) :
    (Nat.floor a ::
      xs.map Nat.floor).Pairwise (· ≤ ·) := by
  rw [List.pairwise_cons]
  constructor
  · intro m hm
    rw [List.mem_map] at hm
    obtain ⟨x, hx, rfl⟩ := hm
    have hax :
        a ≤ x :=
      (List.pairwise_cons.mp hsorted).1 x hx
    exact Nat.floor_mono hax
  · rw [List.pairwise_map]
    exact
      (List.pairwise_cons.mp hsorted).2.imp
        (fun hxy => Nat.floor_mono hxy)

/-- One ordinary real gap can pay only for bands skipped between its endpoint
floor bands. -/
theorem excess_floor_sub_le_skipped
    {x y : ℝ}
    (hx0 : 0 ≤ x)
    (hxy : x ≤ y) :
    excess (Nat.floor (y - x)) ≤
      if Nat.floor x < Nat.floor y then
        Nat.floor y - Nat.floor x - 1
      else 0 := by
  have hgap0 : 0 ≤ y - x := sub_nonneg.mpr hxy
  have hxLo :
      ((Nat.floor x : ℕ) : ℝ) ≤ x :=
    Nat.floor_le hx0
  have hy0 : 0 ≤ y := hx0.trans hxy
  have hyHi :
      y < ((Nat.floor y : ℕ) : ℝ) + 1 :=
    Nat.lt_floor_add_one y
  by_cases hfloor : Nat.floor x < Nat.floor y
  · simp only [if_pos hfloor]
    have hle :
        Nat.floor x ≤ Nat.floor y :=
      Nat.le_of_lt hfloor
    have hcastSub :
        ((Nat.floor y - Nat.floor x : ℕ) : ℝ)
          =
        ((Nat.floor y : ℕ) : ℝ) -
          ((Nat.floor x : ℕ) : ℝ) :=
      Nat.cast_sub hle
    have hgapLt :
        y - x <
          ((Nat.floor y - Nat.floor x + 1 : ℕ) : ℝ) := by
      push_cast
      rw [hcastSub]
      linarith
    have hfloorLe :
        Nat.floor (y - x) ≤
          Nat.floor y - Nat.floor x := by
      have hlt :
          Nat.floor (y - x) <
            Nat.floor y - Nat.floor x + 1 :=
        (Nat.floor_lt hgap0).2
          (by simpa using hgapLt)
      omega
    unfold excess
    omega
  · simp only [if_neg hfloor]
    have hfloorLe :
        Nat.floor y ≤ Nat.floor x := by
      omega
    have hcast :
        ((Nat.floor y : ℕ) : ℝ) ≤
          ((Nat.floor x : ℕ) : ℝ) := by
      exact_mod_cast hfloorLe
    have hgapLt : y - x < 1 := by
      linarith
    have hzero :
        Nat.floor (y - x) = 0 :=
      Nat.floor_eq_zero.mpr ⟨hgap0, hgapLt⟩
    simp [excess, hzero]

/-- Cyclic wrap-gap excess is paid by the bands skipped from the final
occupied band around the top boundary back to the first occupied band. -/
theorem excess_floor_wrap_le_skipped
    {x y t delta : ℝ} {n : ℕ}
    (hx0 : 0 ≤ x)
    (hy0 : 0 ≤ y)
    (hyt : y < t)
    (ht : t = (n : ℝ) + delta)
    (hdelta : delta < 1) :
    excess (Nat.floor (t + x - y)) ≤
      n - Nat.floor y + Nat.floor x := by
  have htSucc :
      t < ((n + 1 : ℕ) : ℝ) := by
    rw [ht]
    push_cast
    linarith
  have hgap0 :
      0 ≤ t + x - y := by
    linarith
  have hxHi :
      x < ((Nat.floor x : ℕ) : ℝ) + 1 :=
    Nat.lt_floor_add_one x
  have hyLo :
      ((Nat.floor y : ℕ) : ℝ) ≤ y :=
    Nat.floor_le hy0
  have hyFloorLt :
      Nat.floor y < n + 1 :=
    (Nat.floor_lt hy0).2
      (by simpa using hyt.trans htSucc.le)
  have hyFloorLe : Nat.floor y ≤ n := by omega
  have hcastSub :
      (((n - Nat.floor y : ℕ) : ℕ) : ℝ) =
        (n : ℝ) - ((Nat.floor y : ℕ) : ℝ) := by
    exact_mod_cast Nat.cast_sub hyFloorLe
  have hgapLt :
      t + x - y <
        ((n - Nat.floor y +
            Nat.floor x + 2 : ℕ) : ℝ) := by
    push_cast
    rw [hcastSub]
    linarith
  have hfloorLt :
      Nat.floor (t + x - y) <
        n - Nat.floor y + Nat.floor x + 2 :=
    (Nat.floor_lt hgap0).2
      (by simpa using hgapLt)
  unfold excess
  omega

/-- Internal successive-gap exponent is bounded by linearly skipped bands. -/
theorem internal_gap_exponent_le_skipped
    (a : ℝ) (xs : List ℝ)
    (ha0 : 0 ≤ a)
    (hsorted : (a :: xs).Pairwise (· ≤ ·))
    (hall0 : ∀ x ∈ a :: xs, 0 ≤ x) :
    listExponent
        ((successiveDiffsFrom a xs).map Nat.floor)
      ≤
    skippedBandCountFrom
      (Nat.floor a) (xs.map Nat.floor) := by
  induction xs generalizing a with
  | nil =>
      simp [successiveDiffsFrom,
        listExponent, skippedBandCountFrom]
  | cons b bs ih =>
      rw [List.pairwise_cons] at hsorted
      have hab : a ≤ b :=
        hsorted.1 b (by simp)
      have hb0 :
          0 ≤ b :=
        hall0 b (by simp)
      have htail :
          (b :: bs).Pairwise (· ≤ ·) :=
        hsorted.2
      have htail0 :
          ∀ x ∈ b :: bs, 0 ≤ x := by
        intro x hx
        exact hall0 x (by simp [hx])
      have hlocal :=
        excess_floor_sub_le_skipped ha0 hab
      have hrec :=
        ih b hb0 htail htail0
      simp only [successiveDiffsFrom,
        List.map_cons, listExponent,
        List.map_cons, List.sum_cons,
        skippedBandCountFrom]
      unfold listExponent at hrec
      omega

/-- Cyclic real gaps at circumference t. -/
def cyclicRealGaps (t : ℝ) : List ℝ → List ℝ
  | [] => []
  | a :: xs =>
      successiveDiffsFrom a xs ++
        [t + a - xs.getLastD a]

def cyclicBandQuotients
    (t : ℝ) (angles : List ℝ) : List ℕ :=
  (cyclicRealGaps t angles).map Nat.floor

/-- Main one-dimensional cyclic band budget. -/
theorem cyclicBand_exponent_add_occupied_le
    {t delta : ℝ} {n : ℕ}
    (a : ℝ) (xs : List ℝ)
    (ha0 : 0 ≤ a)
    (hsorted : (a :: xs).Pairwise (· ≤ ·))
    (hall0 : ∀ x ∈ a :: xs, 0 ≤ x)
    (hallt : ∀ x ∈ a :: xs, x < t)
    (ht : t = (n : ℝ) + delta)
    (hdelta : delta < 1) :
    listExponent (cyclicBandQuotients t (a :: xs)) +
        ((a :: xs).map Nat.floor).toFinset.card
      ≤
    n + 1 := by
  let last := xs.getLastD a
  have hlastMem :
      last ∈ a :: xs :=
    List.getLastD_mem_cons a xs
  have hlastT :
      last < t :=
    hallt last hlastMem
  have hlast0 :
      0 ≤ last :=
    hall0 last hlastMem
  have hfloorSorted :
      (Nat.floor a :: xs.map Nat.floor).Pairwise (· ≤ ·) :=
    floor_list_pairwise a xs hsorted
  have hbandBound :
      ∀ m ∈ Nat.floor a :: xs.map Nat.floor, m ≤ n := by
    intro m hm
    rw [List.mem_cons] at hm
    rcases hm with rfl | hm
    · have haT := hallt a (by simp)
      have htSucc :
          t < ((n + 1 : ℕ) : ℝ) := by
        rw [ht]
        push_cast
        linarith
      have hlt :
          Nat.floor a < n + 1 :=
        (Nat.floor_lt ha0).2
          (haT.trans htSucc.le)
      omega
    · rw [List.mem_map] at hm
      obtain ⟨x, hx, rfl⟩ := hm
      have hx0 := hall0 x (by simp [hx])
      have hxT := hallt x (by simp [hx])
      have htSucc :
          t < ((n + 1 : ℕ) : ℝ) := by
        rw [ht]
        push_cast
        linarith
      have hlt :
          Nat.floor x < n + 1 :=
        (Nat.floor_lt hx0).2
          (hxT.trans htSucc.le)
      omega
  have hmissing :=
    total_skipped_eq_missing_bands
      n (Nat.floor a) (xs.map Nat.floor)
      hfloorSorted hbandBound
  have hinternal :=
    internal_gap_exponent_le_skipped
      a xs ha0 hsorted hall0
  have hwrap :=
    excess_floor_wrap_le_skipped
      ha0 hlast0 hlastT ht hdelta
  have hexpSplit :
      listExponent
          (cyclicBandQuotients t (a :: xs))
        =
      listExponent
          ((successiveDiffsFrom a xs).map Nat.floor) +
        excess (Nat.floor (t + a - last)) := by
    simp [cyclicBandQuotients, cyclicRealGaps,
      listExponent, List.map_append, last]
  have hbands :
      ((a :: xs).map Nat.floor).toFinset.card =
        (Nat.floor a :: xs.map Nat.floor).toFinset.card := by
    rfl
  rw [hexpSplit, hbands]
  omega

#print axioms skipped_add_changes_eq_last_sub_first
#print axioms toFinset_card_eq_changes_add_one
#print axioms total_skipped_eq_missing_bands
#print axioms excess_floor_sub_le_skipped
#print axioms excess_floor_wrap_le_skipped
#print axioms cyclicBand_exponent_add_occupied_le

end JSP000404Research
