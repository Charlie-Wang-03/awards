
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
    List.map_cons, List.getLastD_map]
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

#print axioms natFloor_sub_le_floor_sub
#print axioms natFloor_wrap_le_band_wrap
#print axioms cyclicFloorGaps_le_cyclicBandJumps
#print axioms listExponent_le_of_forall₂_le
#print axioms cyclicFloorGapExponent_le_bandJumpExponent

end JSP000404Research
