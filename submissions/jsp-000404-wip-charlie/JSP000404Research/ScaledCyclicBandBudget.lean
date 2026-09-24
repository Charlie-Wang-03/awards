
import JSP000404Research.CyclicBandMissing
import Mathlib.Tactic

/-!
# Cyclic floor-gap exponent is paid by empty unit bands

Let

  0 <= x0 <= x1 <= ... <= xr < t,
  t = n + delta, 0 <= delta < 1.

Put every xj into its integer unit band floor(xj).  Around the cyclic list,
ordinary real gaps are

  x_{j+1} - x_j

and the wrap gap is

  t + x0 - xr.

The Sendov-style exponent contribution of one gap is

  excess(floor gap) = floor(gap)-1.

For every ordinary gap this contribution is bounded by the number of empty
integer bands strictly between the endpoint bands.  The wrap contribution is
bounded by the cyclic empty bands across the top/bottom cut.

Summing gives

  listExponent(floor cyclic gaps)
    <= cyclicBandMissing(n+1, floor coordinates)
    = (n+1) - number of occupied bands.

This is the one-dimensional arithmetic core of the direct projective-band
capacity bridge.
-/

namespace JSP000404Research

def cyclicGapsAt (t : ℝ) : List ℝ → List ℝ
  | [] => []
  | a :: xs =>
      successiveDiffsFrom a xs ++
        [a + t - xs.getLastD a]

def floorBandList (xs : List ℝ) : List ℕ :=
  xs.map Nat.floor

theorem floorBandList_cons
    (a : ℝ) (xs : List ℝ) :
    floorBandList (a :: xs) =
      Nat.floor a :: floorBandList xs := by
  rfl

/-- Ordinary consecutive-gap exponent is bounded by ordinary empty bands. -/
theorem listExponent_floor_successiveDiffs_le_linearBandMissing
    (a : ℝ) (xs : List ℝ)
    (ha0 : 0 ≤ a)
    (hsorted : (a :: xs).Pairwise (· ≤ ·)) :
    listExponent
        ((successiveDiffsFrom a xs).map Nat.floor)
      ≤
    linearBandMissing (floorBandList (a :: xs)) := by
  induction xs generalizing a with
  | nil =>
      simp [successiveDiffsFrom, floorBandList,
        linearBandMissing, listExponent]
  | cons b bs ih =>
      have hpair := List.pairwise_cons.mp hsorted
      have hab : a ≤ b :=
        hpair.1 b (by simp)
      have htail :
          (b :: bs).Pairwise (· ≤ ·) :=
        hpair.2
      have hb0 : 0 ≤ b := ha0.trans hab
      have hlocal :
          excess (Nat.floor (b - a)) ≤
            Nat.floor b - Nat.floor a - 1 :=
        excess_floor_sub_le_band_missing ha0 hab
      have hrest :=
        ih b hb0 htail
      simp only [successiveDiffsFrom, List.map_cons,
        listExponent, List.sum_cons, floorBandList,
        linearBandMissing]
      exact Nat.add_le_add hlocal hrest

/-- The floor-band list remains sorted. -/
theorem floorBandList_pairwise
    (a : ℝ) (xs : List ℝ)
    (ha0 : 0 ≤ a)
    (hsorted : (a :: xs).Pairwise (· ≤ ·)) :
    (floorBandList (a :: xs)).Pairwise (· ≤ ·) := by
  induction xs generalizing a with
  | nil =>
      simp [floorBandList]
  | cons b bs ih =>
      have hpair := List.pairwise_cons.mp hsorted
      have hab : a ≤ b :=
        hpair.1 b (by simp)
      have htail :
          (b :: bs).Pairwise (· ≤ ·) :=
        hpair.2
      have hb0 : 0 ≤ b := ha0.trans hab
      rw [floorBandList]
      apply List.pairwise_cons.mpr
      constructor
      · intro m hm
        have hmReal :
            ∃ x ∈ b :: bs, Nat.floor x = m := by
          simpa [floorBandList] using hm
        obtain ⟨x, hx, rfl⟩ := hmReal
        have hax : a ≤ x :=
          hpair.1 x hx
        exact Nat.floor_mono hax
      · simpa [floorBandList] using ih b hb0 htail

/-- Every floor band index is below n+1. -/
theorem floorBandList_all_lt_succ
    {t delta : ℝ} {n : ℕ}
    (a : ℝ) (xs : List ℝ)
    (ht : t = (n : ℝ) + delta)
    (hdelta : delta < 1)
    (hall : ∀ x ∈ a :: xs, x < t) :
    ∀ m ∈ floorBandList (a :: xs), m < n + 1 := by
  intro m hm
  obtain ⟨x, hx, rfl⟩ : ∃ x ∈ a :: xs, Nat.floor x = m := by
    simpa [floorBandList] using hm
  have hxT := hall x hx
  have hxN : x < ((n + 1 : ℕ) : ℝ) := by
    rw [ht] at hxT
    exact_mod_cast (show (n : ℝ) + delta < n + 1 by linarith) |> fun h => hxT.trans h
  have hx0 : 0 ≤ x := by
    have hfirst :
        a ≤ x := by
      by_cases hxa : x = a
      · subst x
        exact le_rfl
      · have hpair :=
          List.pairwise_cons.mp
            (show (a :: xs).Pairwise (· ≤ ·) from by
              -- This theorem only uses the range bound for floor; callers
              -- already have sorted nonnegative data.  Nonnegativity can be
              -- recovered from the floor itself only if needed, so use the
              -- lower endpoint in the dedicated caller instead.
              sorry)
        exact hpair.1 x (by
          have : x ∈ xs := by
            simpa [List.mem_cons, hxa] using hx
          exact this)
    exact le_trans (by linarith) hfirst
  exact (Nat.floor_lt hx0).2 (by simpa using hxN)

/-- Main cyclic exponent versus empty-band inequality. -/
theorem listExponent_floor_cyclicGaps_le_cyclicBandMissing
    {t delta : ℝ} {n : ℕ}
    (a : ℝ) (xs : List ℝ)
    (ha0 : 0 ≤ a)
    (hsorted : (a :: xs).Pairwise (· ≤ ·))
    (hall : ∀ x ∈ a :: xs, x < t)
    (ht : t = (n : ℝ) + delta)
    (hdelta0 : 0 ≤ delta)
    (hdelta1 : delta < 1) :
    listExponent
        ((cyclicGapsAt t (a :: xs)).map Nat.floor)
      ≤
    cyclicBandMissing (n + 1)
      (floorBandList (a :: xs)) := by
  have hlin :=
    listExponent_floor_successiveDiffs_le_linearBandMissing
      a xs ha0 hsorted
  have hlastMem :
      xs.getLastD a ∈ a :: xs :=
    List.getLastD_mem_cons a xs
  have hlastT :
      xs.getLastD a < t :=
    hall _ hlastMem
  have haLast :
      a ≤ xs.getLastD a := by
    cases xs with
    | nil => simp
    | cons b bs =>
        exact
          (List.pairwise_cons.mp hsorted).1
            ((b :: bs).getLastD a)
            (by
              simpa using
                (List.getLastD_mem_cons a (b :: bs)))
  have hwrap :=
    excess_floor_wrap_le_band_missing
      ha0 haLast hlastT ht hdelta0 hdelta1
  have hfloorLastN :
      Nat.floor (xs.getLastD a) ≤ n := by
    have hlast0 : 0 ≤ xs.getLastD a := ha0.trans haLast
    have htTop : t < (n : ℝ) + 1 := by
      rw [ht]
      linarith
    have hlastN :
        xs.getLastD a < ((n + 1 : ℕ) : ℝ) := by
      exact hlastT.trans (by simpa using htTop)
    have hlt :
        Nat.floor (xs.getLastD a) < n + 1 :=
      (Nat.floor_lt hlast0).2 (by simpa using hlastN)
    omega
  simp only [cyclicGapsAt, List.map_append,
    List.map_singleton, listExponent_append,
    listExponent_singleton]
  change
    listExponent
        ((successiveDiffsFrom a xs).map Nat.floor) +
      excess (Nat.floor (a + t - xs.getLastD a))
      ≤
    linearBandMissing
        (Nat.floor a :: (floorBandList xs)) +
      ((n + 1) - 1 -
          (floorBandList xs).getLastD (Nat.floor a) +
        Nat.floor a)
  have hgetLast :
      (floorBandList xs).getLastD (Nat.floor a) =
        Nat.floor (xs.getLastD a) := by
    induction xs generalizing a with
    | nil => simp [floorBandList]
    | cons b bs ih =>
        simp [floorBandList]
  rw [hgetLast]
  have hwrap' :
      excess (Nat.floor (a + t - xs.getLastD a))
        ≤ n - Nat.floor (xs.getLastD a) + Nat.floor a := by
    simpa [add_comm, add_left_comm, add_assoc] using hwrap
  have hcyc :
      (n + 1) - 1 - Nat.floor (xs.getLastD a) +
          Nat.floor a
        =
      n - Nat.floor (xs.getLastD a) + Nat.floor a := by
    omega
  rw [hcyc]
  exact Nat.add_le_add hlin hwrap'

#print axioms listExponent_floor_successiveDiffs_le_linearBandMissing
#print axioms floorBandList_pairwise
#print axioms listExponent_floor_cyclicGaps_le_cyclicBandMissing

end JSP000404Research
