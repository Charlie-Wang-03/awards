import JSP000404Research.ResidualSafeSupportBlockerSide
import JSP000404Research.ResidualTranslatedOverlapFullBranch
import JSP000404Research.ResidualPairFlipBlocker
import Mathlib.Tactic

/-!
# Order constraints on one-bit full transitions of support-unsafe pairs

Let u<v be a NoActiveSafe overlap carrier and let c be active at both
endpoints.  Such a coordinate is either outgoing at both endpoints or incoming
at both.

For a one-bit full blocker pair a<b:

* if c is common-outgoing at u,v, then u<a and u<b;
* if c is common-incoming at u,v, then a<v and b<v.

Moreover every full blocker constrains c to the flipped canonical bit. Hence
the common orientation of c at the target pair is the opposite one.

This records the order/orientation alternation obeyed by every lossless
one-bit full transition.
-/

namespace JSP000404Research
namespace OrderedEdgeColoring

theorem oneFlip_full_blockers_right_of_lower_of_commonOutgoing
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    {u v a b : V} {base : Fin n → Bool} {c : Fin n}
    (huv : u < v)
    (huBase : base ∈ retainedCompletionWords C u)
    (hvBase : base ∈ retainedCompletionWords C v)
    (hcu : c ∈ retainedActive C u)
    (hcv : c ∈ retainedActive C v)
    (hcuOut : c ∈ outgoingRetained C u)
    (hcvOut : c ∈ outgoingRetained C v)
    (ha : a ∈ oneFlipFullBlockers C u v c)
    (hb : b ∈ oneFlipFullBlockers C u v c) :
    u < a ∧ u < b := by
  have hbase :
      base ∈ retainedCompletionWords C u ∩
        retainedCompletionWords C v :=
    Finset.mem_inter.mpr ⟨huBase,hvBase⟩
  have haWord :=
    oneFlip_fullBlocker_contains_base C hbase ha
  have hbWord :=
    oneFlip_fullBlocker_contains_base C hbase hb
  exact ⟨
    commonOutgoing_oneFlip_blocker_right_of_lower
      C huv huBase hvBase hcu hcv hcuOut hcvOut haWord,
    commonOutgoing_oneFlip_blocker_right_of_lower
      C huv huBase hvBase hcu hcv hcuOut hcvOut hbWord⟩

theorem oneFlip_full_blockers_left_of_upper_of_commonIncoming
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    {u v a b : V} {base : Fin n → Bool} {c : Fin n}
    (huv : u < v)
    (huBase : base ∈ retainedCompletionWords C u)
    (hvBase : base ∈ retainedCompletionWords C v)
    (hcu : c ∈ retainedActive C u)
    (hcv : c ∈ retainedActive C v)
    (hcuIn : c ∈ incomingRetained C u)
    (hcvIn : c ∈ incomingRetained C v)
    (ha : a ∈ oneFlipFullBlockers C u v c)
    (hb : b ∈ oneFlipFullBlockers C u v c) :
    a < v ∧ b < v := by
  have hbase :
      base ∈ retainedCompletionWords C u ∩
        retainedCompletionWords C v :=
    Finset.mem_inter.mpr ⟨huBase,hvBase⟩
  have haWord :=
    oneFlip_fullBlocker_contains_base C hbase ha
  have hbWord :=
    oneFlip_fullBlocker_contains_base C hbase hb
  exact ⟨
    commonIncoming_oneFlip_blocker_left_of_upper
      C huv huBase hvBase hcu hcv hcuIn hcvIn haWord,
    commonIncoming_oneFlip_blocker_left_of_upper
      C huv huBase hvBase hcu hcv hcuIn hcvIn hbWord⟩

theorem oneFlip_full_blocker_bit_opposite_source
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    {u v w : V} {base : Fin n → Bool} {c : Fin n}
    (huv : u ≠ v)
    (huBase : base ∈ retainedCompletionWords C u)
    (hvBase : base ∈ retainedCompletionWords C v)
    (hcu : c ∈ retainedActive C u)
    (hcv : c ∈ retainedActive C v)
    (hw : w ∈ oneFlipFullBlockers C u v c) :
    c ∈ retainedActive C w ∧
    retainedBit C w c = !(retainedBit C u c) := by
  have hbase :
      base ∈ retainedCompletionWords C u ∩
        retainedCompletionWords C v :=
    Finset.mem_inter.mpr ⟨huBase,hvBase⟩
  have hwWord :=
    oneFlip_fullBlocker_contains_base C hbase hw
  exact one_flip_blocker_capture
    C huv huBase hvBase hcu hcv hwWord

theorem oneFlip_full_pair_orientation_flips_of_commonOutgoing
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    {u v a b : V} {base : Fin n → Bool} {c : Fin n}
    (huv : u ≠ v)
    (huBase : base ∈ retainedCompletionWords C u)
    (hvBase : base ∈ retainedCompletionWords C v)
    (hcu : c ∈ retainedActive C u)
    (hcv : c ∈ retainedActive C v)
    (hcuOut : c ∈ outgoingRetained C u)
    (ha : a ∈ oneFlipFullBlockers C u v c)
    (hb : b ∈ oneFlipFullBlockers C u v c) :
    c ∈ incomingRetained C a ∧
      c ∈ incomingRetained C b := by
  have huFalse :=
    retainedBit_false_of_outgoingRetained C hcuOut
  have haCap :=
    oneFlip_full_blocker_bit_opposite_source
      C huv huBase hvBase hcu hcv ha
  have hbCap :=
    oneFlip_full_blocker_bit_opposite_source
      C huv huBase hvBase hcu hcv hb
  have haTrue : retainedBit C a c = true := by
    rw [haCap.2,huFalse]
    simp
  have hbTrue : retainedBit C b c = true := by
    rw [hbCap.2,huFalse]
    simp
  exact ⟨
    (mem_incomingRetained_iff_retainedBit_true C a c).2
      ⟨haCap.1,haTrue⟩,
    (mem_incomingRetained_iff_retainedBit_true C b c).2
      ⟨hbCap.1,hbTrue⟩⟩

theorem oneFlip_full_pair_orientation_flips_of_commonIncoming
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    {u v a b : V} {base : Fin n → Bool} {c : Fin n}
    (huv : u ≠ v)
    (huBase : base ∈ retainedCompletionWords C u)
    (hvBase : base ∈ retainedCompletionWords C v)
    (hcu : c ∈ retainedActive C u)
    (hcv : c ∈ retainedActive C v)
    (hcuIn : c ∈ incomingRetained C u)
    (ha : a ∈ oneFlipFullBlockers C u v c)
    (hb : b ∈ oneFlipFullBlockers C u v c) :
    c ∈ outgoingRetained C a ∧
      c ∈ outgoingRetained C b := by
  have huTrue :=
    (mem_incomingRetained_iff_retainedBit_true C u c).1 hcuIn
  have haCap :=
    oneFlip_full_blocker_bit_opposite_source
      C huv huBase hvBase hcu hcv ha
  have hbCap :=
    oneFlip_full_blocker_bit_opposite_source
      C huv huBase hvBase hcu hcv hb
  have haFalse : retainedBit C a c = false := by
    rw [haCap.2,huTrue]
    simp
  have hbFalse : retainedBit C b c = false := by
    rw [hbCap.2,huTrue]
    simp
  exact ⟨
    outgoingRetained_of_active_retainedBit_false C haCap.1 haFalse,
    outgoingRetained_of_active_retainedBit_false C hbCap.1 hbFalse⟩

#print axioms oneFlip_full_blockers_right_of_lower_of_commonOutgoing
#print axioms oneFlip_full_blockers_left_of_upper_of_commonIncoming
#print axioms oneFlip_full_pair_orientation_flips_of_commonOutgoing
#print axioms oneFlip_full_pair_orientation_flips_of_commonIncoming

end OrderedEdgeColoring
end JSP000404Research
