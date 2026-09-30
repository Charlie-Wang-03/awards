import JSP000404Research.ResidualSafeSupportDisjointOrientation
import JSP000404Research.ResidualPairFlipBlocker
import Mathlib.Tactic

/-!
# Orientation of blockers in the disjoint-active two-bit branch

For a no-active-safe overlap pair with disjoint retained-active sets, choose

  c active at u,  d active at v.

The previous orientation theorem gives c incoming at u and d outgoing at v.
After flipping both coordinates, every blocker activates at least one of c,d.

* If the blocker activates c, the flipped c-bit is false, hence c is outgoing
  at the blocker.
* If it activates d, the flipped d-bit is true, hence d is incoming at the
  blocker.

This labels every two-bit blocker by an outward orientation opposite to the
corresponding source endpoint.
-/

namespace JSP000404Research
namespace OrderedEdgeColoring

theorem twoFlip_disjointSupport_blocker_outgoingC_or_incomingD
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    {u v w : V}
    {word : Fin n → Bool}
    {c d : Fin n}
    (hno : NoActiveSafeCoordinate C u v)
    (hdisj :
      Disjoint (retainedActive C u) (retainedActive C v))
    (huWord : word ∈ retainedCompletionWords C u)
    (hvWord : word ∈ retainedCompletionWords C v)
    (hcU : c ∈ retainedActive C u)
    (hdV : d ∈ retainedActive C v)
    (hcd : c ≠ d)
    (hw :
      flipBoolWordAt (flipBoolWordAt word c) d ∈
        retainedCompletionWords C w) :
    c ∈ outgoingRetained C w ∨
      d ∈ incomingRetained C w := by
  have hcInU :
      c ∈ incomingRetained C u :=
    active_left_subset_incoming_of_noActiveSafe_disjoint
      C hno hdisj hcU
  have hdOutV :
      d ∈ outgoingRetained C v :=
    active_right_subset_outgoing_of_noActiveSafe_disjoint
      C hno hdisj hdV
  rcases two_flip_blocker_active_one
      C (by
        intro huv
        subst v
        have hcV : c ∈ retainedActive C u := hcU
        exact Finset.disjoint_left.mp hdisj hcU hcV)
      hcd huWord hvWord hcU hdV hw
    with hcW | hdW
  · left
    have hbit :=
      two_flip_blocker_bit_at_first
        C hcd huWord hcU hcW hw
    have huTrue :
        retainedBit C u c = true :=
      (mem_incomingRetained_iff_retainedBit_true C u c).1 hcInU
    rw [huTrue] at hbit
    have hwFalse :
        retainedBit C w c = false := by
      simpa using hbit
    rw [retainedActive_eq_incoming_union_outgoing C w] at hcW
    rcases Finset.mem_union.mp hcW with hInW | hOutW
    · have hwTrue :=
        (mem_incomingRetained_iff_retainedBit_true C w c).1 hInW
      rw [hwFalse] at hwTrue
      contradiction
    · exact hOutW
  · right
    have hbit :=
      two_flip_blocker_bit_at_second
        C hcd hvWord hdV hdW hw
    have hvFalse :
        retainedBit C v d = false :=
      retainedBit_false_of_outgoingRetained C hdOutV
    rw [hvFalse] at hbit
    have hwTrue :
        retainedBit C w d = true := by
      simpa using hbit
    exact (mem_incomingRetained_iff_retainedBit_true C w d).2 hwTrue

#print axioms twoFlip_disjointSupport_blocker_outgoingC_or_incomingD

end OrderedEdgeColoring
end JSP000404Research
