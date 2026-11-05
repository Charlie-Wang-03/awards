import JSP000404Research.OriginalSmallCases
import JSP000404Research.PlanarNinePhaseThreshold

/-!
# Complete original lower bounds through forty points

The nine-phase capacity proves the original second branch at n=4. Combining it with
the preceding cases and the complete first threshold covers every N from three to forty.
-/

namespace JSP000404Research

theorem original_lower_twenty_one_through_thirty_two {N : ℕ}
    (hlo : 21 ≤ N) (hhi : N ≤ 32) : OriginalLowerBound N := by
  have hindex : 4 = Nat.clog 2 N - 1 := by interval_cases N <;> decide
  intro p hp
  obtain ⟨a, b, c, hab, hac, hbc, hangle⟩ := planar_four_fifths_angle hp (by simpa)
  refine ⟨a, b, c, hab, hac, hbc, ?_⟩
  rw [Jsp404.alphaN_of_ge_four (by omega) hindex]
  norm_num
  rw [ite_eq_right (by omega : ¬N ≤ 20)]
  linarith

theorem original_lower_three_through_forty {N : ℕ} (hlo : 3 ≤ N) (hhi : N ≤ 40) :
    OriginalLowerBound N := by
  by_cases htwenty : N ≤ 20
  · exact original_lower_three_through_twenty hlo htwenty
  by_cases hthirtytwo : N ≤ 32
  · exact original_lower_twenty_one_through_thirty_two (by omega) hthirtytwo
  have hindex : 5 = Nat.clog 2 N - 1 := by
    have hN : 33 ≤ N := by omega
    interval_cases N <;> decide
  apply original_lower_first_branch (by omega) hindex
  norm_num
  exact hhi

#print axioms original_lower_twenty_one_through_thirty_two
#print axioms original_lower_three_through_forty

end JSP000404Research
