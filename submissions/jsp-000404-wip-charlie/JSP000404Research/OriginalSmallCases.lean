import JSP000404Research.OriginalFirstBranch
import JSP000404Research.PlanarSmallOddThresholds
import JSP000404Research.PlanarSevenPhaseThreshold

/-!
# Complete original lower bounds through twenty points

The first threshold family and the three-, five-, and seven-phase capacities cover every N
from three through twenty, with the exact formula and ordinary planar quantifiers.
-/

namespace JSP000404Research

theorem original_lower_four : OriginalLowerBound 4 := by
  intro p hp
  obtain ⟨a, b, c, hab, hac, hbc, hangle⟩ := planar_right_angle hp (by norm_num)
  refine ⟨a, b, c, hab, hac, hbc, ?_⟩
  rw [Jsp404.alphaN_of_ge_four (by decide) (n := 1) (by decide)]
  norm_num
  linarith

theorem original_lower_six_through_eight {N : ℕ} (hlo : 6 ≤ N) (hhi : N ≤ 8) :
    OriginalLowerBound N := by
  have hindex : 2 = Nat.clog 2 N - 1 := by interval_cases N <;> decide
  intro p hp
  obtain ⟨a, b, c, hab, hac, hbc, hangle⟩ := planar_two_thirds_angle hp (by simpa)
  refine ⟨a, b, c, hab, hac, hbc, ?_⟩
  rw [Jsp404.alphaN_of_ge_four (by omega) hindex]
  norm_num
  rw [ite_eq_right (by omega : ¬N ≤ 5)]
  linarith

/-- Every originally requested case from three through ten points is unconditional. -/
theorem original_lower_three_through_ten {N : ℕ} (hlo : 3 ≤ N) (hhi : N ≤ 10) :
    OriginalLowerBound N := by
  by_cases hmiddle : 6 ≤ N ∧ N ≤ 8
  · exact original_lower_six_through_eight hmiddle.1 hmiddle.2
  interval_cases N
  · exact original_lower_three
  · exact original_lower_four
  · exact original_lower_first_branch (by decide) (n := 2) (by decide) (by norm_num)
  · omega
  · omega
  · omega
  · exact original_lower_first_branch (by decide) (n := 3) (by decide) (by norm_num)
  · exact original_lower_first_branch (by decide) (n := 3) (by decide) (by norm_num)

theorem original_lower_eleven_through_sixteen {N : ℕ} (hlo : 11 ≤ N) (hhi : N ≤ 16) :
    OriginalLowerBound N := by
  have hindex : 3 = Nat.clog 2 N - 1 := by interval_cases N <;> decide
  intro p hp
  obtain ⟨a, b, c, hab, hac, hbc, hangle⟩ := planar_three_quarters_angle hp (by simpa)
  refine ⟨a, b, c, hab, hac, hbc, ?_⟩
  rw [Jsp404.alphaN_of_ge_four (by omega) hindex]
  norm_num
  rw [ite_eq_right (by omega : ¬N ≤ 10)]
  linarith

theorem original_lower_three_through_twenty {N : ℕ} (hlo : 3 ≤ N) (hhi : N ≤ 20) :
    OriginalLowerBound N := by
  by_cases hten : N ≤ 10
  · exact original_lower_three_through_ten hlo hten
  by_cases hsixteen : N ≤ 16
  · exact original_lower_eleven_through_sixteen (by omega) hsixteen
  have hindex : 4 = Nat.clog 2 N - 1 := by
    have hN : 17 ≤ N := by omega
    interval_cases N <;> decide
  apply original_lower_first_branch (by omega) hindex
  norm_num
  exact hhi

#print axioms original_lower_four
#print axioms original_lower_six_through_eight
#print axioms original_lower_three_through_ten
#print axioms original_lower_eleven_through_sixteen
#print axioms original_lower_three_through_twenty

end JSP000404Research
