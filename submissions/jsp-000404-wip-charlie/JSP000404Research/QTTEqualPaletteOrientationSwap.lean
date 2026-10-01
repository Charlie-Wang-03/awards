import JSP000404Research.ResidualQTTWholeCubeEquality
import JSP000404Research.RetainedOrientation
import JSP000404Research.ResidualSameCodeOrientation
import Mathlib.Tactic

/-!
# One-bit orientation swap for an equal-palette Q/T pair

If two vertices have the same retained-active palette and their retained
canonical codes differ exactly at one active coordinate c, then their incoming
retained sets agree away from c and have opposite membership at c.

Because the active palette is the disjoint union of incoming and outgoing
retained colours, the same is true dually for outgoing membership.

This packages the exact orientation content of a whole-cube Q/T equality.
-/

namespace JSP000404Research
namespace OrderedEdgeColoring

theorem incoming_membership_eq_off_oneBit
    {V : Type*} [LinearOrder V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    {u v : V} {c d : Fin n}
    (hbits :
      ∀ e : Fin n,
        e ∈ retainedActive C u →
        e ≠ c →
        retainedBit C v e = retainedBit C u e)
    (hd : d ∈ retainedActive C u)
    (hdc : d ≠ c) :
    (d ∈ incomingRetained C u ↔
      d ∈ incomingRetained C v) := by
  rw [mem_incomingRetained_iff_retainedBit_true,
      mem_incomingRetained_iff_retainedBit_true]
  rw [hbits d hd hdc]

theorem incoming_membership_ne_at_oneBit
    {V : Type*} [LinearOrder V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    {u v : V} {c : Fin n}
    (hcU : c ∈ retainedActive C u)
    (hbitC :
      retainedBit C v c = !(retainedBit C u c)) :
    (c ∈ incomingRetained C u) ≠
      (c ∈ incomingRetained C v) := by
  rw [mem_incomingRetained_iff_retainedBit_true,
      mem_incomingRetained_iff_retainedBit_true]
  rw [hbitC]
  cases h : retainedBit C u c <;> simp

theorem outgoing_membership_eq_off_oneBit
    {V : Type*} [LinearOrder V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    {u v : V} {c d : Fin n}
    (hactive :
      retainedActive C u = retainedActive C v)
    (hbits :
      ∀ e : Fin n,
        e ∈ retainedActive C u →
        e ≠ c →
        retainedBit C v e = retainedBit C u e)
    (hd : d ∈ retainedActive C u)
    (hdc : d ≠ c) :
    (d ∈ outgoingRetained C u ↔
      d ∈ outgoingRetained C v) := by
  have hdV : d ∈ retainedActive C v := by
    rw [← hactive]
    exact hd
  have hIn :=
    incoming_membership_eq_off_oneBit
      C hbits hd hdc
  rw [retainedActive_eq_incoming_union_outgoing C u] at hd
  rw [retainedActive_eq_incoming_union_outgoing C v] at hdV
  have hdisU :=
    incomingRetained_disjoint_outgoingRetained C u
  have hdisV :=
    incomingRetained_disjoint_outgoingRetained C v
  constructor
  · intro hdOutU
    rcases Finset.mem_union.mp hdV with hdInV | hdOutV
    · have hdInU : d ∈ incomingRetained C u := hIn.mpr hdInV
      exact False.elim
        (Finset.disjoint_left.mp hdisU hdInU hdOutU)
    · exact hdOutV
  · intro hdOutV
    rcases Finset.mem_union.mp hd with hdInU | hdOutU
    · have hdInV : d ∈ incomingRetained C v := hIn.mp hdInU
      exact False.elim
        (Finset.disjoint_left.mp hdisV hdInV hdOutV)
    · exact hdOutU

theorem outgoing_membership_ne_at_oneBit
    {V : Type*} [LinearOrder V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    {u v : V} {c : Fin n}
    (hactive :
      retainedActive C u = retainedActive C v)
    (hcU : c ∈ retainedActive C u)
    (hbitC :
      retainedBit C v c = !(retainedBit C u c)) :
    (c ∈ outgoingRetained C u) ≠
      (c ∈ outgoingRetained C v) := by
  have hcV : c ∈ retainedActive C v := by
    rw [← hactive]
    exact hcU
  have hInNe :=
    incoming_membership_ne_at_oneBit C hcU hbitC
  rw [retainedActive_eq_incoming_union_outgoing C u] at hcU
  rw [retainedActive_eq_incoming_union_outgoing C v] at hcV
  have hdisU :=
    incomingRetained_disjoint_outgoingRetained C u
  have hdisV :=
    incomingRetained_disjoint_outgoingRetained C v
  intro hOutEq
  by_cases hInU : c ∈ incomingRetained C u
  · have hnotOutU : c ∉ outgoingRetained C u := by
      exact Finset.disjoint_left.mp hdisU hInU
    have hnotOutV : c ∉ outgoingRetained C v := by
      intro h
      exact hnotOutU (hOutEq.mpr h)
    have hInV : c ∈ incomingRetained C v := by
      rcases Finset.mem_union.mp hcV with h | h
      · exact h
      · exact False.elim (hnotOutV h)
    exact hInNe ⟨hInU,hInV⟩
  · have hOutU : c ∈ outgoingRetained C u := by
      rcases Finset.mem_union.mp hcU with h | h
      · exact False.elim (hInU h)
      · exact h
    have hOutV : c ∈ outgoingRetained C v := hOutEq.mp hOutU
    have hnotInV : c ∉ incomingRetained C v := by
      intro h
      exact Finset.disjoint_left.mp hdisV h hOutV
    have hInEq :
        (c ∈ incomingRetained C u) =
          (c ∈ incomingRetained C v) := by
      apply propext
      simp [hInU,hnotInV]
    exact hInNe hInEq

theorem QTT_equal_palette_orientation_oneBit
    {V : Type*} [LinearOrder V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    {s y : V}
    {word : Fin n → Bool}
    {cy : Fin n}
    (hactive :
      retainedActive C y = retainedActive C s)
    (hcyY : cy ∈ retainedActive C y)
    (hsQ : word ∈ retainedCompletionWords C s)
    (hyT : word ∈ translatedCompletionWords C y cy) :
    ((cy ∈ incomingRetained C y) ≠
       (cy ∈ incomingRetained C s)) ∧
    ((cy ∈ outgoingRetained C y) ≠
       (cy ∈ outgoingRetained C s)) ∧
    (∀ d : Fin n,
      d ∈ retainedActive C s →
      d ≠ cy →
      ((d ∈ incomingRetained C y ↔ d ∈ incomingRetained C s) ∧
       (d ∈ outgoingRetained C y ↔ d ∈ outgoingRetained C s))) := by
  have hcode :=
    QTT_equal_palette_oneBit_code
      C hactive hcyY hsQ hyT
  have hcyS : cy ∈ retainedActive C s := by
    rw [← hactive]
    exact hcyY
  constructor
  · exact incoming_membership_ne_at_oneBit
      C hcyY hcode.1
  constructor
  · exact outgoing_membership_ne_at_oneBit
      C hactive hcyY hcode.1
  · intro d hdS hdc
    have hdY : d ∈ retainedActive C y := by
      rw [hactive]
      exact hdS
    constructor
    · exact incoming_membership_eq_off_oneBit
        C hcode.2 hdS hdc |>.symm
    · exact outgoing_membership_eq_off_oneBit
        C hactive hdS hdc |>.symm

#print axioms QTT_equal_palette_orientation_oneBit

end OrderedEdgeColoring
end JSP000404Research
