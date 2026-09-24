
import JSP000404Research.CyclicProjectiveGaps
import JSP000404Research.SupportTwoDeletion
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Tactic

/-!
# Cyclic real gaps are dominated by cyclic unit-band jumps

Let

  0 <= x_0 <= ... <= x_{m-1} < width < n+1.

Write c_i=floor(x_i).  The ordinary cyclic direction gaps are

  x_{i+1}-x_i

and the wrap gap

  x_0+width-x_{m-1}.

The corresponding cyclic band jumps are

  c_{i+1}-c_i

and

  (n+1-c_{m-1})+c_0.

Every natural floor of a real cyclic gap is bounded by its band jump.

This is the metric core of the standard-residual one-layer palette bound.
It avoids assigning lattice boundary points to ray gaps, so directions which
lie exactly on a unit-band boundary cause no ambiguity.
-/

namespace JSP000404Research

/-- Successive differences of a nondecreasing natural-number list. -/
def successiveNatDiffsFrom (a : ℕ) : List ℕ → List ℕ
  | [] => []
  | b :: bs => (b - a) :: successiveNatDiffsFrom b bs

/-- Cyclic gaps on a real circle of arbitrary width. -/
def cyclicRealGapsAt (width : ℝ) : List ℝ → List ℝ
  | [] => []
  | a :: xs =>
      successiveDiffsFrom a xs ++
        [a + width - xs.getLastD a]

/-- Cyclic jumps in the n+1 standard band labels 0,...,n. -/
def cyclicBandJumps (n : ℕ) : List ℕ → List ℕ
  | [] => []
  | a :: xs =>
      successiveNatDiffsFrom a xs ++
        [(n + 1 - xs.getLastD a) + a]


theorem map_getLastD_eq
    {α β : Type*}
    (f : α → β) (a : α) (xs : List α) :
    (xs.map f).getLastD (f a) =
      f (xs.getLastD a) := by
  induction xs generalizing a with
  | nil =>
      simp
  | cons b bs ih =>
      simpa [List.getLastD_cons] using ih b

theorem natFloor_sub_le_floor_sub
    {x y : ℝ}
    (hx0 : 0 ≤ x)
    (hxy : x ≤ y) :
    Nat.floor (y - x) ≤
      Nat.floor y - Nat.floor x := by
  have hgap0 : 0 ≤ y - x := sub_nonneg.mpr hxy
  have hfloor :
      Nat.floor x ≤ Nat.floor y :=
    Nat.floor_mono hxy
  apply natFloor_le_of_lt_nat_succ hgap0
  have hxlo :
      ((Nat.floor x : ℕ) : ℝ) ≤ x :=
    Nat.floor_le hx0
  have hyhi :
      y < ((Nat.floor y : ℕ) : ℝ) + 1 :=
    Nat.lt_floor_add_one y
  rw [Nat.cast_sub hfloor]
  push_cast
  linarith

/-- Wrap analogue of natFloor_sub_le_floor_sub. -/
theorem natFloor_wrap_le_band_wrap
    {x y width : ℝ} {n : ℕ}
    (hx0 : 0 ≤ x)
    (hxy : x ≤ y)
    (hyWidth : y < width)
    (hwidth : width < (n : ℝ) + 1) :
    Nat.floor (x + width - y) ≤
      (n + 1 - Nat.floor y) + Nat.floor x := by
  have hy0 : 0 ≤ y := hx0.trans hxy
  have hgap0 : 0 ≤ x + width - y := by
    linarith
  have hyN :
      Nat.floor y ≤ n := by
    have hfloorLt :
        Nat.floor y < n + 1 := by
      apply (Nat.floor_lt hy0).2
      simpa [Nat.cast_add, Nat.cast_one] using
        hyWidth.trans hwidth
    omega
  apply natFloor_le_of_lt_nat_succ hgap0
  have hxhi :
      x < ((Nat.floor x : ℕ) : ℝ) + 1 :=
    Nat.lt_floor_add_one x
  have hylo :
      ((Nat.floor y : ℕ) : ℝ) ≤ y :=
    Nat.floor_le hy0
  rw [Nat.cast_add, Nat.cast_sub hyN]
  push_cast
  linarith

/-- Pointwise domination for all ordinary successive gaps. -/
theorem successiveFloorDiffs_le_successiveBandJumps
    (a : ℝ) (xs : List ℝ)
    (ha0 : 0 ≤ a)
    (hsorted : (a :: xs).Pairwise (· ≤ ·)) :
    List.Forall₂ (· ≤ ·)
      ((successiveDiffsFrom a xs).map Nat.floor)
      (successiveNatDiffsFrom (Nat.floor a)
        (xs.map Nat.floor)) := by
  induction xs generalizing a with
  | nil =>
      exact List.Forall₂.nil
  | cons b bs ih =>
      rw [List.pairwise_cons] at hsorted
      have hab : a ≤ b :=
        hsorted.1 b (by simp)
      have hb0 : 0 ≤ b := ha0.trans hab
      have htail :
          (b :: bs).Pairwise (· ≤ ·) :=
        hsorted.2
      simp only [successiveDiffsFrom,
        successiveNatDiffsFrom, List.map_cons]
      apply List.Forall₂.cons
      · exact natFloor_sub_le_floor_sub ha0 hab
      · exact ih b hb0 htail

/-- Full cyclic floor-gap domination by cyclic band jumps. -/
theorem cyclicFloorGaps_le_cyclicBandJumps
    (a : ℝ) (xs : List ℝ)
    {width : ℝ} (n : ℕ)
    (ha0 : 0 ≤ a)
    (hsorted : (a :: xs).Pairwise (· ≤ ·))
    (hall : ∀ x ∈ a :: xs, x < width)
    (hwidth : width < (n : ℝ) + 1) :
    List.Forall₂ (· ≤ ·)
      ((cyclicRealGapsAt width (a :: xs)).map Nat.floor)
      (cyclicBandJumps n
        ((a :: xs).map Nat.floor)) := by
  have hord :=
    successiveFloorDiffs_le_successiveBandJumps
      a xs ha0 hsorted
  have hlastMem :
      xs.getLastD a ∈ a :: xs :=
    List.getLastD_mem_cons a xs
  have hlastWidth :
      xs.getLastD a < width :=
    hall _ hlastMem
  have hfirstLast :
      a ≤ xs.getLastD a := by
    cases xs with
    | nil =>
        simp
    | cons b bs =>
        rw [List.pairwise_cons] at hsorted
        exact hsorted.1 _ (List.getLastD_mem_cons b bs)
  have hwrap :=
    natFloor_wrap_le_band_wrap
      ha0 hfirstLast hlastWidth hwidth
  simp only [cyclicRealGapsAt, cyclicBandJumps,
    List.map_append, List.map_singleton,
    List.map_cons]
  rw [map_getLastD_eq]
  exact List.Forall₂.append hord
    (List.Forall₂.cons hwrap List.Forall₂.nil)

/-- List exponent is monotone under pointwise quotient domination. -/
theorem listExponent_le_of_forall₂_le
    {qs bs : List ℕ}
    (h : List.Forall₂ (· ≤ ·) qs bs) :
    listExponent qs ≤ listExponent bs := by
  induction h with
  | nil =>
      simp [listExponent]
  | @cons q b qs bs hqb hrest ih =>
      simp only [listExponent, List.map_cons, List.sum_cons]
      have hex : excess q ≤ excess b := by
        unfold excess
        omega
      omega

/-- Exponent consequence of cyclic band-gap domination. -/
theorem cyclicFloorGapExponent_le_bandJumpExponent
    (a : ℝ) (xs : List ℝ)
    {width : ℝ} (n : ℕ)
    (ha0 : 0 ≤ a)
    (hsorted : (a :: xs).Pairwise (· ≤ ·))
    (hall : ∀ x ∈ a :: xs, x < width)
    (hwidth : width < (n : ℝ) + 1) :
    listExponent
        ((cyclicRealGapsAt width (a :: xs)).map Nat.floor)
      ≤
    listExponent
        (cyclicBandJumps n
          ((a :: xs).map Nat.floor)) := by
  exact listExponent_le_of_forall₂_le
    (cyclicFloorGaps_le_cyclicBandJumps
      a xs n ha0 hsorted hall hwidth)


/-- Sum of successive natural differences telescopes on a nondecreasing list. -/
theorem successiveNatDiffsFrom_sum
    (a : ℕ) (xs : List ℕ)
    (hsorted : (a :: xs).Pairwise (· ≤ ·)) :
    (successiveNatDiffsFrom a xs).sum =
      xs.getLastD a - a := by
  induction xs generalizing a with
  | nil =>
      simp [successiveNatDiffsFrom]
  | cons b bs ih =>
      rw [List.pairwise_cons] at hsorted
      have hab : a ≤ b :=
        hsorted.1 b (by simp)
      have htail :
          (b :: bs).Pairwise (· ≤ ·) :=
        hsorted.2
      have hih := ih b htail
      simp only [successiveNatDiffsFrom,
        List.sum_cons, hih, List.getLastD_cons]
      cases bs with
      | nil =>
          simp
          omega
      | cons d ds =>
          have hbLast :
              b ≤ (d :: ds).getLastD b := by
            have hpair :
                ∀ x ∈ d :: ds, b ≤ x := by
              exact (List.pairwise_cons.mp htail).1
            exact hpair _ (List.getLastD_mem_cons d ds)
          omega

/-- Cyclic band jumps telescope to exactly n+1. -/
theorem cyclicBandJumps_sum
    (n a : ℕ) (xs : List ℕ)
    (hsorted : (a :: xs).Pairwise (· ≤ ·))
    (hall : ∀ x ∈ a :: xs, x ≤ n) :
    (cyclicBandJumps n (a :: xs)).sum = n + 1 := by
  have hsucc :=
    successiveNatDiffsFrom_sum a xs hsorted
  have hlastMem :
      xs.getLastD a ∈ a :: xs :=
    List.getLastD_mem_cons a xs
  have hlastN :
      xs.getLastD a ≤ n :=
    hall _ hlastMem
  have hfirstLast :
      a ≤ xs.getLastD a := by
    cases xs with
    | nil =>
        simp
    | cons b bs =>
        rw [List.pairwise_cons] at hsorted
        exact hsorted.1 _ (List.getLastD_mem_cons b bs)
  simp only [cyclicBandJumps, List.sum_append,
    List.sum_singleton, hsucc]
  omega

theorem listPositiveCount_append
    (xs ys : List ℕ) :
    listPositiveCount (xs ++ ys) =
      listPositiveCount xs + listPositiveCount ys := by
  induction xs with
  | nil =>
      simp [listPositiveCount]
  | cons x xs ih =>
      by_cases hx : x = 0
      · simp [listPositiveCount, hx, ih]
      · simp [listPositiveCount, hx, ih, add_assoc]

theorem listPositiveCount_singleton_of_pos
    {q : ℕ} (hq : 1 ≤ q) :
    listPositiveCount [q] = 1 := by
  simp [listPositiveCount]
  omega

/-- The wrap band jump is always positive when the last used band is <= n. -/
theorem bandWrapJump_pos
    {n a last : ℕ}
    (hlast : last ≤ n) :
    1 ≤ (n + 1 - last) + a := by
  omega

/-- Positive cyclic jumps count the distinct labels of a sorted band list. -/
theorem cyclicBandJumps_positiveCount_eq_toFinset_card
    (n a : ℕ) (xs : List ℕ)
    (hsorted : (a :: xs).Pairwise (· ≤ ·))
    (hall : ∀ x ∈ a :: xs, x ≤ n) :
    listPositiveCount (cyclicBandJumps n (a :: xs)) =
      (a :: xs).toFinset.card := by
  classical
  induction xs generalizing a with
  | nil =>
      have haN : a ≤ n := hall a (by simp)
      have hwrap : 1 ≤ (n + 1 - a) + a :=
        bandWrapJump_pos (a := a) haN
      simp [cyclicBandJumps, successiveNatDiffsFrom,
        listPositiveCount, hwrap.ne']
  | cons b bs ih =>
      rw [List.pairwise_cons] at hsorted
      have hab : a ≤ b :=
        hsorted.1 b (by simp)
      have htail :
          (b :: bs).Pairwise (· ≤ ·) :=
        hsorted.2
      have hallTail :
          ∀ x ∈ b :: bs, x ≤ n := by
        intro x hx
        exact hall x (by simp [hx])
      have hih := ih b htail hallTail
      have hlastN :
          (b :: bs).getLastD b ≤ n := by
        exact hallTail _ (List.getLastD_mem_cons b bs)
      have hwrapA :
          1 ≤ (n + 1 - (b :: bs).getLastD b) + a :=
        bandWrapJump_pos hlastN
      have hwrapB :
          1 ≤ (n + 1 - (b :: bs).getLastD b) + b :=
        bandWrapJump_pos hlastN
      have htailCount :
          listPositiveCount
              (successiveNatDiffsFrom b bs ++
                [(n + 1 - bs.getLastD b) + b])
            =
          listPositiveCount (successiveNatDiffsFrom b bs) + 1 := by
        rw [listPositiveCount_append]
        have hlastN' : bs.getLastD b ≤ n := by
          exact hallTail _ (List.getLastD_mem_cons b bs)
        rw [listPositiveCount_singleton_of_pos
          (bandWrapJump_pos hlastN')]
      by_cases heq : a = b
      · subst a
        simpa [cyclicBandJumps, successiveNatDiffsFrom,
          listPositiveCount] using hih
      · have hablt : a < b := lt_of_le_of_ne hab heq
        have haNot : a ∉ (b :: bs).toFinset := by
          intro haMem
          have haList : a ∈ b :: bs := by
            simpa using haMem
          simp only [List.mem_cons] at haList
          rcases haList with habEq | haBs
          · exact heq habEq.symm
          · have hba : b ≤ a :=
              (List.pairwise_cons.mp htail).1 a haBs
            omega
        have hfirstPos : 1 ≤ b - a := by
          omega
        have hwrapA' :
            1 ≤ (n + 1 - bs.getLastD b) + a := by
          have hlastN' : bs.getLastD b ≤ n := by
            exact hallTail _ (List.getLastD_mem_cons b bs)
          exact bandWrapJump_pos hlastN'
        have hleft :
            listPositiveCount
              (cyclicBandJumps n (a :: b :: bs))
              =
            listPositiveCount
              (cyclicBandJumps n (b :: bs)) + 1 := by
          simp only [cyclicBandJumps, successiveNatDiffsFrom]
          rw [listPositiveCount_append,
              listPositiveCount_append]
          rw [listPositiveCount_singleton_of_pos hwrapA',
              listPositiveCount_singleton_of_pos
                (bandWrapJump_pos
                  (hallTail _ (List.getLastD_mem_cons b bs)))]
          simp [listPositiveCount, hfirstPos.ne', add_assoc,
            add_comm, add_left_comm]
        rw [hleft, hih]
        simp [List.toFinset_cons, haNot]

/-- List zero-carry identity. -/
theorem listExponent_add_listPositiveCount
    (qs : List ℕ) :
    listExponent qs + listPositiveCount qs = qs.sum := by
  induction qs with
  | nil =>
      simp [listExponent, listPositiveCount]
  | cons q qs ih =>
      by_cases hq : q = 0
      · subst q
        simp [listExponent, listPositiveCount, excess, ih]
      · have hpos : 1 ≤ q := Nat.one_le_iff_ne_zero.mpr hq
        simp [listExponent, listPositiveCount, excess, hq, ih]
        omega

/-- Exact exponent of cyclic band jumps. -/
theorem cyclicBandJumps_exponent_eq_total_sub_distinct
    (n a : ℕ) (xs : List ℕ)
    (hsorted : (a :: xs).Pairwise (· ≤ ·))
    (hall : ∀ x ∈ a :: xs, x ≤ n) :
    listExponent (cyclicBandJumps n (a :: xs)) =
      (n + 1) - (a :: xs).toFinset.card := by
  have hid :=
    listExponent_add_listPositiveCount
      (cyclicBandJumps n (a :: xs))
  rw [cyclicBandJumps_sum n a xs hsorted hall,
      cyclicBandJumps_positiveCount_eq_toFinset_card
        n a xs hsorted hall] at hid
  omega

/-- Floor labels of a sorted nonnegative real list remain sorted. -/
theorem floorLabels_pairwise
    (a : ℝ) (xs : List ℝ)
    (hsorted : (a :: xs).Pairwise (· ≤ ·)) :
    ((a :: xs).map Nat.floor).Pairwise (· ≤ ·) := by
  rw [List.pairwise_map]
  exact hsorted.imp fun x y hxy =>
    Nat.floor_mono hxy

/-- All floor labels lie in 0,...,n when every direction is below n+1. -/
theorem floorLabel_le_n_of_lt_n_succ
    {x : ℝ} {n : ℕ}
    (hx0 : 0 ≤ x)
    (hx : x < (n : ℝ) + 1) :
    Nat.floor x ≤ n := by
  have hlt :
      Nat.floor x < n + 1 := by
    exact (Nat.floor_lt hx0).2
      (by simpa [Nat.cast_add, Nat.cast_one] using hx)
  omega

/-- Complete abstract standard-residual local budget on a sorted direction
list: cyclic gap exponent plus the number of used unit bands is at most n+1. -/
theorem cyclicFloorGapExponent_add_usedBands_le
    (a : ℝ) (xs : List ℝ)
    {width : ℝ} (n : ℕ)
    (ha0 : 0 ≤ a)
    (hsorted : (a :: xs).Pairwise (· ≤ ·))
    (hall0 : ∀ x ∈ a :: xs, 0 ≤ x)
    (hallWidth : ∀ x ∈ a :: xs, x < width)
    (hwidth : width < (n : ℝ) + 1) :
    listExponent
        ((cyclicRealGapsAt width (a :: xs)).map Nat.floor)
      +
      ((a :: xs).map Nat.floor).toFinset.card
      ≤
    n + 1 := by
  have hExp :=
    cyclicFloorGapExponent_le_bandJumpExponent
      a xs n ha0 hsorted hallWidth hwidth
  have hlabelSorted :=
    floorLabels_pairwise a xs hsorted
  have hlabelBound :
      ∀ c ∈ (a :: xs).map Nat.floor, c ≤ n := by
    intro c hc
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hc
    exact floorLabel_le_n_of_lt_n_succ
      (hall0 x hx)
      ((hallWidth x hx).trans hwidth)
  have hBandExp :=
    cyclicBandJumps_exponent_eq_total_sub_distinct
      n (Nat.floor a) (xs.map Nat.floor)
      (by simpa using hlabelSorted)
      (by
        intro c hc
        exact hlabelBound c (by simpa using hc))
  rw [hBandExp] at hExp
  omega

#print axioms successiveNatDiffsFrom_sum
#print axioms cyclicBandJumps_sum
#print axioms cyclicBandJumps_positiveCount_eq_toFinset_card
#print axioms cyclicBandJumps_exponent_eq_total_sub_distinct
#print axioms cyclicFloorGapExponent_add_usedBands_le

#print axioms natFloor_sub_le_floor_sub
#print axioms natFloor_wrap_le_band_wrap
#print axioms cyclicFloorGaps_le_cyclicBandJumps
#print axioms listExponent_le_of_forall₂_le
#print axioms cyclicFloorGapExponent_le_bandJumpExponent

end JSP000404Research
