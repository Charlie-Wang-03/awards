import JSP000404Research.FourCycleBandCloseness
import Mathlib.Tactic

/-!
# Owner-choice rigidity in the ordered adjacent four-cycle

For an interior whole-cube source, the two partner-pair edges straddling the
source each have two possible owner colours.  The ordered-adjacent small-angle
terminal makes the four K2,2 edge labels pairwise one-step close around the
cycle.

With three distinct owner labels, any use of the third owner on one of those
ambiguous cross edges would make all three owner labels pairwise one-step
close, impossible in Nat.  Hence both ambiguous edges are forced onto the two
same-side owner colours, leaving the two-colour staircase pattern.
-/

namespace JSP000404Research

theorem natOneStepClose_symm
    {x y : ℕ}
    (h : NatOneStepClose x y) :
    NatOneStepClose y x := by
  exact ⟨h.2,h.1⟩

theorem three_distinct_pairwise_oneStep_impossible
    (x y z : ℕ)
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (hXY : NatOneStepClose x y)
    (hXZ : NatOneStepClose x z)
    (hYZ : NatOneStepClose y z) :
    False := by
  unfold NatOneStepClose at hXY hXZ hYZ
  omega

theorem interior_source_owner_choices_force_two_colour_staircase
    (x y z u v : ℕ)
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (hu : u = x ∨ u = y)
    (hv : v = x ∨ v = z)
    (hYZ : NatOneStepClose y z)
    (hUY : NatOneStepClose u y)
    (hVZ : NatOneStepClose v z)
    (hUV : NatOneStepClose u v) :
    u = y ∧ v = z := by
  rcases hu with rfl | rfl
  · rcases hv with rfl | rfl
    · exact False.elim
        (three_distinct_pairwise_oneStep_impossible
          x y z hxy hxz hyz hUY hVZ hYZ)
    · exact False.elim
        (three_distinct_pairwise_oneStep_impossible
          x y z hxy hxz hyz hUY hUV hYZ)
  · rcases hv with rfl | rfl
    · exact False.elim
        (three_distinct_pairwise_oneStep_impossible
          x y z hxy hxz hyz (natOneStepClose_symm hUV) hVZ hYZ)
    · exact ⟨rfl,rfl⟩

#print axioms three_distinct_pairwise_oneStep_impossible
#print axioms interior_source_owner_choices_force_two_colour_staircase

end JSP000404Research
