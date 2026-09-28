import JSP000404Research.LinearBandGapCapacity
import JSP000404Research.FloorMergeCarry
import JSP000404Research.PinnedCyclicDeletionGain
import Mathlib.Tactic

/-!
# One-unit gain from deleting a value flanked by positive cyclic floor gaps

Work directly on normalized cut coordinates on a circle of width t.

For a sorted displayed segment

  a <= b <= c

inside

  a :: b :: c :: xs,

deleting b merges the two consecutive gaps b-a and c-b into c-a.  The floor
of the merged gap is

  floor(c-a) = floor(b-a) + floor(c-b) + carry,

with binary carry.  Therefore if both parent gap quotients are positive, the
cyclic list exponent rises by at least one.

A symmetric final-position theorem handles deletion of the last displayed
value when its predecessor gap and cyclic wrap gap are both positive.

These are the cut-normalized list backends for the non-top support-three
deletion outlet.
-/

namespace JSP000404Research

theorem linearCyclicGapQuotients_cons_cons_cons
    (t a b c : ℝ) (xs : List ℝ) :
    linearCyclicGapQuotients t (a :: b :: c :: xs)
      =
    Nat.floor (b - a) ::
      Nat.floor (c - b) ::
      ((successiveDiffsFrom c xs).map Nat.floor ++
        [Nat.floor (a + t - xs.getLastD c)]) := by
  simp [linearCyclicGapQuotients, successiveDiffsFrom,
    List.getLastD_cons, List.append_assoc]

theorem linearCyclicGapQuotients_delete_second
    {t a b c : ℝ} {xs : List ℝ}
    (hab : a ≤ b)
    (hbc : b ≤ c) :
    ∃ carry : ℕ,
      carry ≤ 1 ∧
      linearCyclicGapQuotients t (a :: c :: xs)
        =
      (Nat.floor (b - a) + Nat.floor (c - b) + carry) ::
        ((successiveDiffsFrom c xs).map Nat.floor ++
          [Nat.floor (a + t - xs.getLastD c)]) := by
  have hg1 : 0 ≤ b - a := sub_nonneg.mpr hab
  have hg2 : 0 ≤ c - b := sub_nonneg.mpr hbc
  obtain ⟨carry,hcarry,hmerge⟩ :=
    natFloor_scaled_gap_merge
      (t := (1 : ℝ)) (g₁ := b - a) (g₂ := c - b)
      (by norm_num) hg1 hg2
  refine ⟨carry,hcarry,?_⟩
  simp only [linearCyclicGapQuotients,
    successiveDiffsFrom, List.map_cons, List.getLastD_cons]
  have hsum :
      (c - b) + (b - a) = c - a := by ring
  have hmerge' :
      Nat.floor (c - a) =
        Nat.floor (b - a) + Nat.floor (c - b) + carry := by
    have h := hmerge
    norm_num at h
    rw [show (b - a) + (c - b) = c - a by ring] at h
    exact h
  rw [hmerge']

/-- Deleting the second displayed value gains one exponent unit when both
adjacent ordinary floor gaps are positive. -/
theorem listExponent_linearCyclic_delete_second_gain
    {t a b c : ℝ} {xs : List ℝ}
    (hab : a ≤ b)
    (hbc : b ≤ c)
    (hLeft : 1 ≤ Nat.floor (b - a))
    (hRight : 1 ≤ Nat.floor (c - b)) :
    listExponent
        (linearCyclicGapQuotients t (a :: b :: c :: xs)) + 1
      ≤
    listExponent
        (linearCyclicGapQuotients t (a :: c :: xs)) := by
  obtain ⟨carry,_hcarry,hchild⟩ :=
    linearCyclicGapQuotients_delete_second
      (t := t) (a := a) (b := b) (c := c) (xs := xs)
      hab hbc
  rw [linearCyclicGapQuotients_cons_cons_cons,
      hchild]
  let tail :=
    (successiveDiffsFrom c xs).map Nat.floor ++
      [Nat.floor (a + t - xs.getLastD c)]
  have hlocal :=
    excess_merge_gain_of_both_pos
      (a := Nat.floor (b - a))
      (b := Nat.floor (c - b))
      (c := carry)
      hLeft hRight
  simp only [listExponent, List.map_cons, List.sum_cons]
  dsimp [tail]
  omega

/-- Explicit cyclic quotient form for a nonempty displayed list ending in z. -/
theorem linearCyclicGapQuotients_append_last
    (t a : ℝ) (pre : List ℝ) (z : ℝ) :
    linearCyclicGapQuotients t (a :: (pre ++ [z]))
      =
    (successiveDiffsFrom a pre).map Nat.floor ++
      [Nat.floor (z - pre.getLastD a),
       Nat.floor (a + t - z)] := by
  induction pre generalizing a with
  | nil =>
      simp [linearCyclicGapQuotients, successiveDiffsFrom]
  | cons b bs ih =>
      simp only [List.cons_append, linearCyclicGapQuotients,
        successiveDiffsFrom, List.map_cons, List.getLastD_cons]
      rw [successiveDiffsFrom_append_cons]
      simp [List.map_append, List.append_assoc]

/-- Final displayed deletion merges predecessor and wrap gaps. -/
theorem listExponent_linearCyclic_delete_last_gain
    {t a z : ℝ} {pre : List ℝ}
    (hpre :
      pre ≠ [])
    (hLeft :
      1 ≤ Nat.floor (z - pre.getLastD a))
    (hWrap :
      1 ≤ Nat.floor (a + t - z))
    (horder :
      pre.getLastD a ≤ z)
    (hwrap0 :
      0 ≤ a + t - z) :
    listExponent
        (linearCyclicGapQuotients t (a :: (pre ++ [z]))) + 1
      ≤
    listExponent
        (linearCyclicGapQuotients t (a :: pre)) := by
  let y := pre.getLastD a
  have hleft0 : 0 ≤ z - y := sub_nonneg.mpr horder
  obtain ⟨carry,_hcarry,hmerge⟩ :=
    natFloor_scaled_gap_merge
      (t := (1 : ℝ))
      (g₁ := z - y) (g₂ := a + t - z)
      (by norm_num) hleft0 hwrap0
  have hsum :
      (z - y) + (a + t - z) = a + t - y := by ring
  have hmerge' :
      Nat.floor (a + t - y) =
        Nat.floor (z - y) +
          Nat.floor (a + t - z) + carry := by
    have h := hmerge
    norm_num at h
    rw [hsum] at h
    exact h
  have hpreDecomp :
      ∃ first mid,
        pre = first :: mid := by
    cases hp : pre with
    | nil => exact False.elim (hpre hp)
    | cons first mid => exact ⟨first,mid,hp⟩
  obtain ⟨first,mid,rfl⟩ := hpreDecomp
  rw [linearCyclicGapQuotients_append_last]
  simp only [linearCyclicGapQuotients,
    successiveDiffsFrom, List.map_cons, List.getLastD_cons]
  have hparent :
      (successiveDiffsFrom a (first :: mid)).map Nat.floor ++
          [Nat.floor (z - (first :: mid).getLastD a),
           Nat.floor (a + t - z)]
        =
      Nat.floor (first - a) ::
        ((successiveDiffsFrom first mid).map Nat.floor ++
          [Nat.floor (z - mid.getLastD first),
           Nat.floor (a + t - z)]) := by
    simp [successiveDiffsFrom, List.getLastD_cons,
      List.append_assoc]
  rw [hparent]
  have hchild :
      linearCyclicGapQuotients t (a :: first :: mid)
        =
      Nat.floor (first - a) ::
        ((successiveDiffsFrom first mid).map Nat.floor ++
          [Nat.floor (a + t - mid.getLastD first)]) := by
    simp [linearCyclicGapQuotients, successiveDiffsFrom,
      List.getLastD_cons, List.append_assoc]
  rw [hchild]
  have hy :
      (first :: mid).getLastD a = mid.getLastD first := by
    simp [List.getLastD_cons]
  rw [hy] at hLeft horder hmerge'
  have hlocal :=
    excess_merge_gain_of_both_pos
      (a := Nat.floor (z - mid.getLastD first))
      (b := Nat.floor (a + t - z))
      (c := carry)
      hLeft hWrap
  simp only [listExponent, List.map_cons, List.sum_cons,
    List.map_append, List.sum_append, List.map_singleton,
    List.sum_singleton]
  rw [hmerge']
  omega

#print axioms linearCyclicGapQuotients_delete_second
#print axioms listExponent_linearCyclic_delete_second_gain
#print axioms listExponent_linearCyclic_delete_last_gain

end JSP000404Research
