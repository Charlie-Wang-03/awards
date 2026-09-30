import JSP000404Research.ResidualTranslatedOverlapFullPair
import JSP000404Research.ResidualSameCodeOrientation
import Mathlib.Tactic

/-!
# One-bit full transitions consume their displacement coordinate

For a one-bit translated overlap, every full blocker constrains the displaced
coordinate to the opposite canonical bit from the source pair. Hence two
distinct full blockers constrain that coordinate to the same bit.

Since two distinct full blockers form a residual pair, a retained coordinate
which is active at both endpoints and has the same canonical bit must lie in
the residual forbidden list of that new pair:

* bit true  => incoming at the lower endpoint;
* bit false => outgoing at the upper endpoint.

Therefore the one-bit displacement coordinate becomes forbidden on the new
full-blocker residual pair. A full transition cannot immediately reuse the
same coordinate as a safe residual target.
-/

namespace JSP000404Research
namespace OrderedEdgeColoring

theorem outgoingRetained_of_active_retainedBit_false
    {V : Type*} [LinearOrder V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    {v : V} {c : Fin n}
    (hc : c ∈ retainedActive C v)
    (hbit : retainedBit C v c = false) :
    c ∈ outgoingRetained C v := by
  rw [retainedActive_eq_incoming_union_outgoing C v] at hc
  rcases Finset.mem_union.mp hc with hin | hout
  · have htrue :=
      (mem_incomingRetained_iff_retainedBit_true C v c).1 hin
    rw [hbit] at htrue
    simp at htrue
  · exact hout

theorem oneFlip_two_fullBlockers_forbid_displacement
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    {u v w z : V} {c : Fin n}
    {base : Fin n → Bool}
    (huv : u ≠ v)
    (hbase :
      base ∈ retainedCompletionWords C u ∩
        retainedCompletionWords C v)
    (hcu : c ∈ retainedActive C u)
    (hcv : c ∈ retainedActive C v)
    (hw : w ∈ oneFlipFullBlockers C u v c)
    (hz : z ∈ oneFlipFullBlockers C u v c)
    (hwz : w ≠ z) :
    (
      w < z ∧
      IsResidual C w z ∧
      c ∈ residualForbidden C w z
    )
    ∨
    (
      z < w ∧
      IsResidual C z w ∧
      c ∈ residualForbidden C z w
    ) := by
  have hparts := Finset.mem_inter.mp hbase
  have hyW :=
    oneFlip_fullBlocker_contains_base C hbase hw
  have hyZ :=
    oneFlip_fullBlocker_contains_base C hbase hz
  have hcapW :=
    one_flip_blocker_capture
      C huv hparts.1 hparts.2 hcu hcv hyW
  have hcapZ :=
    one_flip_blocker_capture
      C huv hparts.1 hparts.2 hcu hcv hyZ
  have hbitEq :
      retainedBit C w c = retainedBit C z c := by
    rw [hcapW.2, hcapZ.2]
  rcases oneFlip_two_fullBlockers_form_residual_pair
      C hbase hw hz hwz
    with hres | hres
  · left
    refine ⟨hres.1,hres.2,?_⟩
    by_cases hbit : retainedBit C w c = true
    · apply Finset.mem_union_left
      exact
        (mem_incomingRetained_iff_retainedBit_true C w c).2
          ⟨hcapW.1,hbit⟩
    · have hfalse : retainedBit C w c = false := by
        cases hb : retainedBit C w c <;> simp_all
      have hfalseZ : retainedBit C z c = false := by
        rw [← hbitEq]
        exact hfalse
      apply Finset.mem_union_right
      exact outgoingRetained_of_active_retainedBit_false
        C hcapZ.1 hfalseZ
  · right
    refine ⟨hres.1,hres.2,?_⟩
    by_cases hbit : retainedBit C z c = true
    · apply Finset.mem_union_left
      exact
        (mem_incomingRetained_iff_retainedBit_true C z c).2
          ⟨hcapZ.1,hbit⟩
    · have hfalse : retainedBit C z c = false := by
        cases hb : retainedBit C z c <;> simp_all
      have hfalseW : retainedBit C w c = false := by
        rw [hbitEq]
        exact hfalse
      apply Finset.mem_union_right
      exact outgoingRetained_of_active_retainedBit_false
        C hcapW.1 hfalseW

#print axioms outgoingRetained_of_active_retainedBit_false
#print axioms oneFlip_two_fullBlockers_forbid_displacement

end OrderedEdgeColoring
end JSP000404Research
