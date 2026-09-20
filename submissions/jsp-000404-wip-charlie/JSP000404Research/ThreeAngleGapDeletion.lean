import JSP000404Research.CyclicProjectiveGaps
import JSP000404Research.CentreQuotientData
import JSP000404Research.FloorMergeCarry
import Mathlib.Tactic

/-!
# Deleting one angle from a three-ray projective cycle

For sorted canonical projective parameters

  a <= b <= c,   0 <= a,   c < pi,

the normalized three-cycle gaps are

  g0 = (b-a)/pi,
  g1 = (c-b)/pi,
  g2 = (a+pi-c)/pi.

Deleting one ray merges exactly the two cyclic gaps adjacent to it:

* delete b: [g0+g1, g2];
* delete a: [g1, g2+g0];
* delete c: [g0, g1+g2].

At fixed nonnegative scale t, FloorMergeCarry then proves that the actual child
quotient profile is exactly the corresponding parent quotient merge with a
binary carry.

This is the angle-list half of the concrete four-to-three deletion bridge.
-/

namespace JSP000404Research

open Real

theorem normalizedProjectiveGaps_three
    (a b c : ℝ) :
    normalizedProjectiveGaps [a,b,c] =
      [(b-a)/Real.pi,
       (c-b)/Real.pi,
       (a+Real.pi-c)/Real.pi] := by
  simp [normalizedProjectiveGaps, projectiveGaps, successiveDiffsFrom]

theorem normalizedProjectiveGaps_two
    (a b : ℝ) :
    normalizedProjectiveGaps [a,b] =
      [(b-a)/Real.pi,
       (a+Real.pi-b)/Real.pi] := by
  simp [normalizedProjectiveGaps, projectiveGaps, successiveDiffsFrom]

/-- Delete the middle ray: the two ordinary gaps merge. -/
theorem normalizedProjectiveGaps_delete_middle_three
    (a b c : ℝ) :
    normalizedProjectiveGaps [a,c] =
      [((b-a)/Real.pi) + ((c-b)/Real.pi),
       (a+Real.pi-c)/Real.pi] := by
  rw [normalizedProjectiveGaps_two]
  congr 1
  field_simp [Real.pi_ne_zero]
  ring

/-- Delete the first ray: the old wrap gap merges with the first ordinary gap. -/
theorem normalizedProjectiveGaps_delete_first_three
    (a b c : ℝ) :
    normalizedProjectiveGaps [b,c] =
      [(c-b)/Real.pi,
       ((a+Real.pi-c)/Real.pi) + ((b-a)/Real.pi)] := by
  rw [normalizedProjectiveGaps_two]
  congr 1
  field_simp [Real.pi_ne_zero]
  ring

/-- Delete the last ray: the last ordinary gap merges with the old wrap gap. -/
theorem normalizedProjectiveGaps_delete_last_three
    (a b c : ℝ) :
    normalizedProjectiveGaps [a,b] =
      [(b-a)/Real.pi,
       ((c-b)/Real.pi) + ((a+Real.pi-c)/Real.pi)] := by
  rw [normalizedProjectiveGaps_two]
  congr 1
  field_simp [Real.pi_ne_zero]
  ring

/-- Fixed-t quotient update after deleting the middle ray. -/
theorem quotientList_delete_middle_three
    {a b c t : ℝ}
    (hab : a ≤ b) (hbc : b ≤ c)
    (ht : 0 ≤ t) :
    ∃ carry : ℕ,
      carry ≤ 1 ∧
      quotientList t (normalizedProjectiveGaps [a,c]) =
        [Nat.floor (t*((b-a)/Real.pi)) +
           Nat.floor (t*((c-b)/Real.pi)) + carry,
         Nat.floor (t*((a+Real.pi-c)/Real.pi))] := by
  have hg0 : 0 ≤ (b-a)/Real.pi :=
    div_nonneg (sub_nonneg.mpr hab) Real.pi_pos.le
  have hg1 : 0 ≤ (c-b)/Real.pi :=
    div_nonneg (sub_nonneg.mpr hbc) Real.pi_pos.le
  obtain ⟨carry, hc, hmerge⟩ :=
    natFloor_scaled_gap_merge ht hg0 hg1
  refine ⟨carry, hc, ?_⟩
  rw [normalizedProjectiveGaps_delete_middle_three]
  simp only [quotientList, List.map_cons, List.map_nil]
  rw [hmerge]

/-- Fixed-t quotient update after deleting the first ray. -/
theorem quotientList_delete_first_three
    {a b c t : ℝ}
    (ha0 : 0 ≤ a)
    (hab : a ≤ b) (hbc : b ≤ c)
    (hcpi : c < Real.pi)
    (ht : 0 ≤ t) :
    ∃ carry : ℕ,
      carry ≤ 1 ∧
      quotientList t (normalizedProjectiveGaps [b,c]) =
        [Nat.floor (t*((c-b)/Real.pi)),
         Nat.floor (t*((a+Real.pi-c)/Real.pi)) +
           Nat.floor (t*((b-a)/Real.pi)) + carry] := by
  have hg2 : 0 ≤ (a+Real.pi-c)/Real.pi := by
    apply div_nonneg
    · linarith
    · exact Real.pi_pos.le
  have hg0 : 0 ≤ (b-a)/Real.pi :=
    div_nonneg (sub_nonneg.mpr hab) Real.pi_pos.le
  obtain ⟨carry, hc, hmerge⟩ :=
    natFloor_scaled_gap_merge ht hg2 hg0
  refine ⟨carry, hc, ?_⟩
  rw [normalizedProjectiveGaps_delete_first_three]
  simp only [quotientList, List.map_cons, List.map_nil]
  rw [hmerge]

/-- Fixed-t quotient update after deleting the last ray. -/
theorem quotientList_delete_last_three
    {a b c t : ℝ}
    (ha0 : 0 ≤ a)
    (hab : a ≤ b) (hbc : b ≤ c)
    (hcpi : c < Real.pi)
    (ht : 0 ≤ t) :
    ∃ carry : ℕ,
      carry ≤ 1 ∧
      quotientList t (normalizedProjectiveGaps [a,b]) =
        [Nat.floor (t*((b-a)/Real.pi)),
         Nat.floor (t*((c-b)/Real.pi)) +
           Nat.floor (t*((a+Real.pi-c)/Real.pi)) + carry] := by
  have hg1 : 0 ≤ (c-b)/Real.pi :=
    div_nonneg (sub_nonneg.mpr hbc) Real.pi_pos.le
  have hg2 : 0 ≤ (a+Real.pi-c)/Real.pi := by
    apply div_nonneg
    · linarith
    · exact Real.pi_pos.le
  obtain ⟨carry, hc, hmerge⟩ :=
    natFloor_scaled_gap_merge ht hg1 hg2
  refine ⟨carry, hc, ?_⟩
  rw [normalizedProjectiveGaps_delete_last_three]
  simp only [quotientList, List.map_cons, List.map_nil]
  rw [hmerge]

#print axioms normalizedProjectiveGaps_delete_middle_three
#print axioms normalizedProjectiveGaps_delete_first_three
#print axioms normalizedProjectiveGaps_delete_last_three
#print axioms quotientList_delete_middle_three
#print axioms quotientList_delete_first_three
#print axioms quotientList_delete_last_three

end JSP000404Research
