import JSP000404Research.ThreeColourPaletteHelly
import Mathlib.Tactic

/-!
# Endpoint rigidity of three-consecutive palettes

Two length-three natural intervals which both contain the same pair of labels
at distance exactly two must coincide.
-/

namespace JSP000404Research

theorem threeNatInterval_start_eq_of_common_distance_two
    {m r u v : ℕ}
    (hum : u ∈ threeNatInterval m)
    (hvm : v ∈ threeNatInterval m)
    (hur : u ∈ threeNatInterval r)
    (hvr : v ∈ threeNatInterval r)
    (hdist : u + 2 = v ∨ v + 2 = u) :
    r = m := by
  rw [mem_threeNatInterval_iff_bounds] at hum hvm hur hvr
  rcases hdist with h | h <;> omega

theorem threeNatInterval_eq_of_common_distance_two
    {m r u v : ℕ}
    (hum : u ∈ threeNatInterval m)
    (hvm : v ∈ threeNatInterval m)
    (hur : u ∈ threeNatInterval r)
    (hvr : v ∈ threeNatInterval r)
    (hdist : u + 2 = v ∨ v + 2 = u) :
    threeNatInterval r = threeNatInterval m := by
  rw [threeNatInterval_start_eq_of_common_distance_two
    hum hvm hur hvr hdist]

/-- Conversely, in a three-consecutive interval, any two members at distance
two are exactly its two endpoints. -/
theorem common_distance_two_are_threeNatInterval_endpoints
    {m u v : ℕ}
    (hu : u ∈ threeNatInterval m)
    (hv : v ∈ threeNatInterval m)
    (hdist : u + 2 = v ∨ v + 2 = u) :
    (u = m ∧ v = m + 2) ∨
    (v = m ∧ u = m + 2) := by
  rw [mem_threeNatInterval_iff_bounds] at hu hv
  rcases hdist with h | h
  · left; omega
  · right; omega

#print axioms threeNatInterval_start_eq_of_common_distance_two
#print axioms threeNatInterval_eq_of_common_distance_two
#print axioms common_distance_two_are_threeNatInterval_endpoints

end JSP000404Research
