import JSP000404Research.ResidualFullTransitionOrder
import Mathlib.Tactic

/-!
# Order type of a same-coordinate two-cycle of one-bit full transitions

Suppose u<v translates along a common-outgoing coordinate c to two distinct
full blockers a<b.  The target pair has c common-incoming.

If translating the target pair back along the same coordinate has u and v as
full blockers, then blocker-side geometry gives

  u < a,   v < b.

For two disjoint ordered pairs this excludes both nested order types.  Hence
only two configurations remain:

  u < v < a < b        (separated),
  u < a < v < b        (crossing).

This is the exact linear-order shape of a same-coordinate lossless 2-cycle.
-/

namespace JSP000404Research
namespace OrderedEdgeColoring

theorem two_disjoint_pairs_of_lower_upper_inequalities_separated_or_crossing
    {V : Type*} [LinearOrder V]
    {u v a b : V}
    (huv : u < v)
    (hab : a < b)
    (hua : u < a)
    (hvb : v < b)
    (huA : u ≠ a)
    (huB : u ≠ b)
    (hvA : v ≠ a)
    (hvB : v ≠ b) :
    (u < v ∧ v < a ∧ a < b)
    ∨
    (u < a ∧ a < v ∧ v < b) := by
  rcases lt_or_gt_of_ne hvA with hva | hav
  · exact Or.inl ⟨huv,hva,hab⟩
  · exact Or.inr ⟨hua,hav,hvb⟩

theorem same_coordinate_full_two_cycle_separated_or_crossing
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    {u v a b : V} {base : Fin n → Bool} {c : Fin n}
    (huv : u < v)
    (hab : a < b)
    (huBase : base ∈ retainedCompletionWords C u)
    (hvBase : base ∈ retainedCompletionWords C v)
    (hcu : c ∈ retainedActive C u)
    (hcv : c ∈ retainedActive C v)
    (hcuOut : c ∈ outgoingRetained C u)
    (hcvOut : c ∈ outgoingRetained C v)
    (ha : a ∈ oneFlipFullBlockers C u v c)
    (hb : b ∈ oneFlipFullBlockers C u v c)
    (huBack : u ∈ oneFlipFullBlockers C a b c)
    (hvBack : v ∈ oneFlipFullBlockers C a b c)
    (hdisj :
      u ≠ a ∧ u ≠ b ∧ v ≠ a ∧ v ≠ b) :
    (u < v ∧ v < a ∧ a < b)
    ∨
    (u < a ∧ a < v ∧ v < b) := by
  have hright :=
    oneFlip_full_blockers_right_of_lower_of_commonOutgoing
      C huv huBase hvBase hcu hcv hcuOut hcvOut ha hb
  have htargetIn :=
    oneFlip_full_pair_orientation_flips_of_commonOutgoing
      C (ne_of_lt huv) huBase hvBase hcu hcv hcuOut ha hb
  have hyA :
      flipBoolWordAt base c ∈ retainedCompletionWords C a := by
    exact oneFlip_fullBlocker_contains_base
      C (Finset.mem_inter.mpr ⟨huBase,hvBase⟩) ha
  have hyB :
      flipBoolWordAt base c ∈ retainedCompletionWords C b := by
    exact oneFlip_fullBlocker_contains_base
      C (Finset.mem_inter.mpr ⟨huBase,hvBase⟩) hb
  have hleft :=
    oneFlip_full_blockers_left_of_upper_of_commonIncoming
      C hab hyA hyB
      (incomingRetained_subset_retainedActive C a htargetIn.1)
      (incomingRetained_subset_retainedActive C b htargetIn.2)
      htargetIn.1 htargetIn.2 huBack hvBack
  exact
    two_disjoint_pairs_of_lower_upper_inequalities_separated_or_crossing
      huv hab hright.1 hleft.2
      hdisj.1 hdisj.2.1 hdisj.2.2.1 hdisj.2.2.2

#print axioms two_disjoint_pairs_of_lower_upper_inequalities_separated_or_crossing
#print axioms same_coordinate_full_two_cycle_separated_or_crossing

end OrderedEdgeColoring
end JSP000404Research
