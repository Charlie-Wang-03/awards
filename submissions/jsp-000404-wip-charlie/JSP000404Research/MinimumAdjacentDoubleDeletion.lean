import JSP000404Research.ConcreteAdjacentDoubleDeletionRigidity
import JSP000404Research.ConcreteSecondDeletionRigidity
import Mathlib.Tactic

/-!
# Adjacent minimum rays in a rigid two-deletion chain

This module composes the exact-mass deletion rigidity with the concrete
adjacent double-deletion theorem.

Let r be a first minimum centre whose deletion column is rigid at mass 2^n.
Let s be another minimum centre in the first child, and suppose the second
deletion child is bounded by 2^n.  At every survivor i strictly above the
minimum exponent layer:

* the first deletion leaves the exponent at i unchanged;
* the second deletion also leaves it unchanged.

If the parent rays i->r and i->s are adjacent and interior in the sorted
projective cycle, ConcreteAdjacentDoubleDeletionRigidity applies.  Hence at
least two of the three parent quotient gaps surrounding those two rays vanish.

This is the first direct local planar consequence of two successive
inductively bounded minimum deletions.
-/

namespace JSP000404Research

theorem adjacent_two_minimum_deletions_force_three_gap_sparse_at_high_survivor
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane} (hp : Function.Injective p)
    (C : ∀ i : V, CentreProjectiveCycle hp i)
    (hcard : 4 ≤ Fintype.card V)
    {t : ℝ}
    (ht : 0 ≤ t)
    (n a : ℕ)
    (r s i : V)
    (hsr : s ≠ r)
    (hir : i ≠ r)
    (his : i ≠ s)
    (hsExp : centreExponent (C s) t = a)
    (hiHigh : a < centreExponent (C i) t)
    (hpostR :
      deletionPostWeight
          (concreteDeletionAfter C (by omega) t) r
        = 2 ^ n)
    (hrigidR :
      ∀ j : V, j ≠ r →
        concreteDeletionAfter C (by omega) t r j =
          centreExponent (C j) t)
    (hgrand :
      deletionPostWeight
        (concreteDeletionAfter
          (deletedCycleFamily C (by omega) r)
          (three_le_card_deletedVertexType r hcard)
          t)
        (childVertex r s hsr)
        ≤ 2 ^ n)
    (first : OtherVertex i)
    (mid tail : List (OtherVertex i))
    (next : OtherVertex i)
    (hrays :
      (C i).rays =
        first ::
          (mid ++
            deletedParentRay r i hir ::
            deletedParentRay s i his ::
            next :: tail)) :
    let theta := rayThetaAt hp i
    let prev := (mid.map theta).getLastD (theta first)
    let x := theta (deletedParentRay r i hir)
    let y := theta (deletedParentRay s i his)
    let z := theta next
    let q0 := Nat.floor (t * ((x - prev) / Real.pi))
    let q1 := Nat.floor (t * ((y - x) / Real.pi))
    let q2 := Nat.floor (t * ((z - y) / Real.pi))
    (q0 = 0 ∧ q1 = 0) ∨
    (q0 = 0 ∧ q2 = 0) ∨
    (q1 = 0 ∧ q2 = 0) := by
  let hparent3 : 3 ≤ Fintype.card V := by omega
  let hotherR :
      Nonempty
        (OtherVertex
          (survivingCentre r i hir)) :=
    child_other_nonempty_of_card_ge_three
      hparent3 hir
  let sChild : DeletedVertexType r :=
    childVertex r s hsr
  let iChild : DeletedVertexType r :=
    childVertex r i hir
  have hisChild : iChild ≠ sChild := by
    intro h
    apply his
    exact congrArg Subtype.val h
  let hchild3 :
      3 ≤ Fintype.card (DeletedVertexType r) :=
    three_le_card_deletedVertexType r hcard
  let hotherS :
      Nonempty
        (OtherVertex
          (survivingCentre sChild iChild hisChild)) :=
    child_other_nonempty_of_card_ge_three
      hchild3 hisChild

  have hEq1 :
      centreExponent
          ((C i).restrictDelete r hir hotherR) t
        =
      centreExponent (C i) t := by
    have h := hrigidR i hir
    rw [concreteDeletionAfter_eq
      C hparent3 t hir] at h
    simpa [hotherR, hparent3] using h

  have hSecond :=
    concrete_secondDeletion_exponent_eq_above_min
      C hcard ht n a r s i hsr hir his
      hsExp hiHigh hpostR hrigidR hgrand

  have hChildCycle :
      deletedCycleFamily C hparent3 r iChild =
        (C i).restrictDelete r hir hotherR := by
    have h :=
      deletedCycleFamily_at_survivingCentre_eq_restrictDelete
        C hparent3 r i hir
    simpa [iChild, childVertex, hotherR, hparent3,
      survivingCentre] using h

  have hEq2 :
      centreExponent
          (((C i).restrictDelete r hir hotherR).restrictDelete
            sChild hisChild hotherS) t
        =
      centreExponent
          ((C i).restrictDelete r hir hotherR) t := by
    dsimp at hSecond
    rw [hChildCycle] at hSecond
    simpa [sChild, iChild, hchild3, hotherS,
      hparent3] using hSecond

  exact
    concrete_adjacent_double_deletion_triple_shape
      hp (C i) hir his hsr.symm hotherR
      first mid tail next hrays ht hotherS
      hEq1 hEq2

#print axioms adjacent_two_minimum_deletions_force_three_gap_sparse_at_high_survivor

end JSP000404Research
