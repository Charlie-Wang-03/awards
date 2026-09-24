
import JSP000404Research.PinnedCyclicDeletionGain
import Mathlib.Data.List.Pairwise
import Mathlib.Data.List.ToFinset
import Mathlib.Tactic

/-!
# Empty unit bands around a sorted cyclic coordinate list

Let

  m0 <= m1 <= ... <= mr

be the integer unit-band indices occupied by a nonempty sorted list of real
coordinates.

For each ordinary consecutive pair, the number of unit bands strictly between
them is

  next - prev - 1

with truncated natural subtraction.  The cyclic wrap contributes

  K - 1 - last + first

when all indices are below K.

The sum of these cyclic missing-band counts is exactly

  K - card({occupied band indices}).

This file also records the local floor estimate: the floor excess of a real
gap between two coordinates is bounded by the number of missing unit bands
between their floor indices.  A corresponding wrap estimate holds when the
total circle width t satisfies t<K.

These are the one-dimensional combinatorial facts behind the direct
projective-band active-colour budget.
-/

namespace JSP000404Research

def linearBandMissing : List ℕ → ℕ
  | [] => 0
  | [_] => 0
  | a :: b :: xs =>
      (b - a - 1) + linearBandMissing (b :: xs)

def cyclicBandMissing (K : ℕ) : List ℕ → ℕ
  | [] => 0
  | a :: xs =>
      linearBandMissing (a :: xs) +
        (K - 1 - xs.getLastD a + a)

/-- Sorted band indices have an exact linear missing-band identity. -/
theorem linearBandMissing_add_toFinset_card
    (a : ℕ) (xs : List ℕ)
    (hsorted : (a :: xs).Pairwise (· ≤ ·)) :
    linearBandMissing (a :: xs) +
        (a :: xs).toFinset.card
      =
    xs.getLastD a - a + 1 := by
  induction xs generalizing a with
  | nil =>
      simp [linearBandMissing]
  | cons b bs ih =>
      have hpair :=
        List.pairwise_cons.mp hsorted
      have hab : a ≤ b :=
        hpair.1 b (by simp)
      have htail : (b :: bs).Pairwise (· ≤ ·) :=
        hpair.2
      have hih :=
        ih b htail
      by_cases habEq : a = b
      · subst b
        simpa [linearBandMissing] using hih
      · have habLt : a < b := lt_of_le_of_ne hab habEq
        have haNot :
            a ∉ b :: bs := by
          intro haMem
          simp only [List.mem_cons] at haMem
          rcases haMem with hba | haBs
          · omega
          · have htailPair :=
              List.pairwise_cons.mp htail
            have hba :
                b ≤ a :=
              htailPair.1 a haBs
            omega
        have haNotFin :
            a ∉ (b :: bs).toFinset := by
          simpa using haNot
        simp only [linearBandMissing]
        rw [List.toFinset_cons,
            Finset.card_insert_of_not_mem haNotFin]
        rw [List.getLastD_cons]
        have hlastGe :
            b ≤ bs.getLastD b := by
          cases bs with
          | nil => simp
          | cons c cs =>
              have hmem :
                  bs.getLastD b ∈ b :: c :: cs := by
                exact List.getLastD_mem_cons b (c :: cs)
              exact
                (List.pairwise_cons.mp htail).1
                  (bs.getLastD b) (by
                    simpa using hmem)
        omega

/-- Exact cyclic missing-band count. -/
theorem cyclicBandMissing_add_toFinset_card
    (K a : ℕ) (xs : List ℕ)
    (hsorted : (a :: xs).Pairwise (· ≤ ·))
    (hbound : ∀ m ∈ a :: xs, m < K) :
    cyclicBandMissing K (a :: xs) +
        (a :: xs).toFinset.card
      =
    K := by
  have hlin :=
    linearBandMissing_add_toFinset_card
      a xs hsorted
  have haK : a < K :=
    hbound a (by simp)
  have hlastK :
      xs.getLastD a < K := by
    exact hbound _ (List.getLastD_mem_cons a xs)
  have haLast :
      a ≤ xs.getLastD a := by
    cases xs with
    | nil => simp
    | cons b bs =>
        have hmem :
            (b :: bs).getLastD a ∈ a :: b :: bs :=
          List.getLastD_mem_cons a (b :: bs)
        exact
          (List.pairwise_cons.mp hsorted).1
            ((b :: bs).getLastD a)
            (by simpa using hmem)
  unfold cyclicBandMissing
  omega

theorem cyclicBandMissing_eq_complement_card
    (K a : ℕ) (xs : List ℕ)
    (hsorted : (a :: xs).Pairwise (· ≤ ·))
    (hbound : ∀ m ∈ a :: xs, m < K) :
    cyclicBandMissing K (a :: xs) =
      K - (a :: xs).toFinset.card := by
  have h :=
    cyclicBandMissing_add_toFinset_card
      K a xs hsorted hbound
  omega

/-- Ordinary gap floor is bounded by the jump of the endpoint band indices. -/
theorem natFloor_sub_le_floor_sub_floor
    {x y : ℝ}
    (hx0 : 0 ≤ x)
    (hxy : x ≤ y) :
    Nat.floor (y - x) ≤
      Nat.floor y - Nat.floor x := by
  let a := Nat.floor x
  let b := Nat.floor y
  have haLo : (a : ℝ) ≤ x :=
    Nat.floor_le hx0
  have hy0 : 0 ≤ y := hx0.trans hxy
  have hbHi : y < (b : ℝ) + 1 :=
    Nat.lt_floor_add_one y
  have hab : a ≤ b := by
    exact Nat.floor_mono hxy
  have hgap0 : 0 ≤ y - x := sub_nonneg.mpr hxy
  have hgap :
      y - x < ((b - a : ℕ) : ℝ) + 1 := by
    have hcast :
        ((b - a : ℕ) : ℝ) = (b : ℝ) - (a : ℝ) := by
      exact Nat.cast_sub hab
    rw [hcast]
    linarith
  exact natFloor_le_of_lt_count_succ hgap0 hgap

/-- Ordinary quotient excess is paid by strictly intermediate empty bands. -/
theorem excess_floor_sub_le_band_missing
    {x y : ℝ}
    (hx0 : 0 ≤ x)
    (hxy : x ≤ y) :
    excess (Nat.floor (y - x)) ≤
      Nat.floor y - Nat.floor x - 1 := by
  have hq :=
    natFloor_sub_le_floor_sub_floor hx0 hxy
  unfold excess
  omega

/-- Wrap-gap floor bound for a circle of width t=n+delta<n+1. -/
theorem natFloor_wrap_le
    {x y t delta : ℝ} {n : ℕ}
    (hx0 : 0 ≤ x)
    (hxy : x ≤ y)
    (hyT : y < t)
    (ht : t = (n : ℝ) + delta)
    (hdelta0 : 0 ≤ delta)
    (hdelta1 : delta < 1) :
    Nat.floor (t + x - y) ≤
      (n + 1) - Nat.floor y + Nat.floor x := by
  let a := Nat.floor x
  let b := Nat.floor y
  have hy0 : 0 ≤ y := hx0.trans hxy
  have haHi : x < (a : ℝ) + 1 :=
    Nat.lt_floor_add_one x
  have hbLo : (b : ℝ) ≤ y :=
    Nat.floor_le hy0
  have hbN :
      b ≤ n := by
    have htTop : t < (n : ℝ) + 1 := by
      rw [ht]
      linarith
    have hyN : y < (n : ℝ) + 1 :=
      hyT.trans htTop
    have hfloorLt : Nat.floor y < n + 1 := by
      exact (Nat.floor_lt hy0).2 (by simpa using hyN)
    omega
  have hgap0 :
      0 ≤ t + x - y := by
    have ht0 : 0 ≤ t := by
      rw [ht]
      exact add_nonneg (by positivity) hdelta0
    have hyx : y - x ≤ t := by
      linarith
    linarith
  have hgap :
      t + x - y <
        (((n + 1) - b + a : ℕ) : ℝ) + 1 := by
    have hsubCast :
        (((n + 1) - b : ℕ) : ℝ) =
          ((n + 1 : ℕ) : ℝ) - (b : ℝ) := by
      exact Nat.cast_sub (by omega : b ≤ n + 1)
    push_cast
    rw [hsubCast]
    rw [ht]
    linarith
  exact natFloor_le_of_lt_count_succ hgap0 hgap

/-- Wrap quotient excess is paid by the cyclic empty bands. -/
theorem excess_floor_wrap_le_band_missing
    {x y t delta : ℝ} {n : ℕ}
    (hx0 : 0 ≤ x)
    (hxy : x ≤ y)
    (hyT : y < t)
    (ht : t = (n : ℝ) + delta)
    (hdelta0 : 0 ≤ delta)
    (hdelta1 : delta < 1) :
    excess (Nat.floor (t + x - y)) ≤
      n - Nat.floor y + Nat.floor x := by
  have hq :=
    natFloor_wrap_le
      hx0 hxy hyT ht hdelta0 hdelta1
  unfold excess
  omega

#print axioms linearBandMissing_add_toFinset_card
#print axioms cyclicBandMissing_add_toFinset_card
#print axioms natFloor_sub_le_floor_sub_floor
#print axioms excess_floor_sub_le_band_missing
#print axioms natFloor_wrap_le
#print axioms excess_floor_wrap_le_band_missing

end JSP000404Research
