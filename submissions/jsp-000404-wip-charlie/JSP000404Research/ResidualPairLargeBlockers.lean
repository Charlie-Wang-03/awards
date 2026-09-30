import JSP000404Research.ResidualPairBlockerIncidence
import Mathlib.Tactic

/-!
# At most three large blockers for one pair displacement

Call a blocker large if it captures strictly more than half of the source
overlap mass under a fixed one- or two-bit displacement.

The total blocker-incidence budget is at most twice the source mass. Four
large blockers would therefore contribute strictly more than twice the source
mass, a contradiction.

Hence the dimension-preserving / full-capacity branch has constant fan-out:
at most three blocker vertices for each fixed carrier displacement.
-/

namespace JSP000404Research
namespace OrderedEdgeColoring

noncomputable def oneFlipLargeBlockers
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (u v : V) (c : Fin n) : Finset V := by
  classical
  exact (Finset.univ : Finset V).filter
    (fun w =>
      (retainedCompletionWords C u ∩
        retainedCompletionWords C v).card
        <
      2 * (oneFlipCapturedSourceWords C u v w c).card)

noncomputable def twoFlipLargeBlockers
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (u v : V) (c d : Fin n) : Finset V := by
  classical
  exact (Finset.univ : Finset V).filter
    (fun w =>
      (retainedCompletionWords C u ∩
        retainedCompletionWords C v).card
        <
      2 * (twoFlipCapturedSourceWords C u v w c d).card)

@[simp] theorem mem_oneFlipLargeBlockers
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (u v w : V) (c : Fin n) :
    w ∈ oneFlipLargeBlockers C u v c ↔
      (retainedCompletionWords C u ∩
        retainedCompletionWords C v).card
        <
      2 * (oneFlipCapturedSourceWords C u v w c).card := by
  classical
  simp [oneFlipLargeBlockers]

@[simp] theorem mem_twoFlipLargeBlockers
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (u v w : V) (c d : Fin n) :
    w ∈ twoFlipLargeBlockers C u v c d ↔
      (retainedCompletionWords C u ∩
        retainedCompletionWords C v).card
        <
      2 * (twoFlipCapturedSourceWords C u v w c d).card := by
  classical
  simp [twoFlipLargeBlockers]

theorem oneFlipLargeBlockers_card_le_three
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (u v : V) (c : Fin n) :
    (oneFlipLargeBlockers C u v c).card ≤ 3 := by
  classical
  let L := oneFlipLargeBlockers C u v c
  let m :=
    (retainedCompletionWords C u ∩
      retainedCompletionWords C v).card
  by_contra h
  have h4 : 4 ≤ L.card := by omega
  have hL : L.Nonempty := Finset.card_pos.mp (by omega)
  have hstrict :
      (∑ _w ∈ L, m)
        <
      ∑ w ∈ L,
        2 * (oneFlipCapturedSourceWords C u v w c).card := by
    apply Finset.sum_lt_sum_of_nonempty hL
    intro w hw
    exact (mem_oneFlipLargeBlockers C u v w c).1 hw
  have hsumSub :
      (∑ w ∈ L,
        (oneFlipCapturedSourceWords C u v w c).card)
        ≤
      ∑ w : V,
        (oneFlipCapturedSourceWords C u v w c).card := by
    simpa [L] using
      (Finset.sum_le_sum_of_subset
        (Finset.filter_subset
          (Finset.univ : Finset V)
          (fun w =>
            (retainedCompletionWords C u ∩
              retainedCompletionWords C v).card
              <
            2 * (oneFlipCapturedSourceWords C u v w c).card))
        : (∑ w ∈ L,
            (oneFlipCapturedSourceWords C u v w c).card)
          ≤
          ∑ w ∈ (Finset.univ : Finset V),
            (oneFlipCapturedSourceWords C u v w c).card)
  have htotal :=
    sum_oneFlipCaptured_le_two_mul_overlap
      C (u := u) (v := v) (c := c)
  have h4m : 4 * m ≤ L.card * m :=
    Nat.mul_le_mul_right m h4
  have hstrict' :
      L.card * m
        <
      2 * (∑ w ∈ L,
        (oneFlipCapturedSourceWords C u v w c).card) := by
    simpa [Finset.sum_const_nat, Finset.mul_sum, Nat.mul_comm] using hstrict
  have hupper :
      2 * (∑ w ∈ L,
        (oneFlipCapturedSourceWords C u v w c).card)
        ≤ 4 * m := by
    have h1 :=
      Nat.mul_le_mul_left 2 hsumSub
    have h2 :=
      Nat.mul_le_mul_left 2 htotal
    dsimp [m] at h2 ⊢
    omega
  omega

theorem twoFlipLargeBlockers_card_le_three
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (u v : V) (c d : Fin n) :
    (twoFlipLargeBlockers C u v c d).card ≤ 3 := by
  classical
  let L := twoFlipLargeBlockers C u v c d
  let m :=
    (retainedCompletionWords C u ∩
      retainedCompletionWords C v).card
  by_contra h
  have h4 : 4 ≤ L.card := by omega
  have hL : L.Nonempty := Finset.card_pos.mp (by omega)
  have hstrict :
      (∑ _w ∈ L, m)
        <
      ∑ w ∈ L,
        2 * (twoFlipCapturedSourceWords C u v w c d).card := by
    apply Finset.sum_lt_sum_of_nonempty hL
    intro w hw
    exact (mem_twoFlipLargeBlockers C u v w c d).1 hw
  have hsumSub :
      (∑ w ∈ L,
        (twoFlipCapturedSourceWords C u v w c d).card)
        ≤
      ∑ w : V,
        (twoFlipCapturedSourceWords C u v w c d).card := by
    simpa [L] using
      (Finset.sum_le_sum_of_subset
        (Finset.filter_subset
          (Finset.univ : Finset V)
          (fun w =>
            (retainedCompletionWords C u ∩
              retainedCompletionWords C v).card
              <
            2 * (twoFlipCapturedSourceWords C u v w c d).card))
        : (∑ w ∈ L,
            (twoFlipCapturedSourceWords C u v w c d).card)
          ≤
          ∑ w ∈ (Finset.univ : Finset V),
            (twoFlipCapturedSourceWords C u v w c d).card)
  have htotal :=
    sum_twoFlipCaptured_le_two_mul_overlap
      C (u := u) (v := v) (c := c) (d := d)
  have h4m : 4 * m ≤ L.card * m :=
    Nat.mul_le_mul_right m h4
  have hstrict' :
      L.card * m
        <
      2 * (∑ w ∈ L,
        (twoFlipCapturedSourceWords C u v w c d).card) := by
    simpa [Finset.sum_const_nat, Finset.mul_sum, Nat.mul_comm] using hstrict
  have hupper :
      2 * (∑ w ∈ L,
        (twoFlipCapturedSourceWords C u v w c d).card)
        ≤ 4 * m := by
    have h1 :=
      Nat.mul_le_mul_left 2 hsumSub
    have h2 :=
      Nat.mul_le_mul_left 2 htotal
    dsimp [m] at h2 ⊢
    omega
  omega

#print axioms oneFlipLargeBlockers_card_le_three
#print axioms twoFlipLargeBlockers_card_le_three

end OrderedEdgeColoring
end JSP000404Research
