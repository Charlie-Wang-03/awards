import JSP000404Research.ConcreteSecondDeletionRigidity
import JSP000404Research.ConcreteAdjacentDoubleDeletionRigidity
import Mathlib.Tactic

/-!
# Adjacent minimum rays at a higher survivor force a sparse parent triple

This file closes the concrete bridge needed by the two-minimum induction route.

Assume r and s lie in the same minimum exponent layer, r is deleted first,
the r-column is rigid with exact post mass 2^n, and the grandchild obtained by
then deleting s is bounded by 2^n.  At any survivor i strictly above that
minimum layer:

* the first deletion leaves exponent(i) unchanged by root-column rigidity;
* the second deletion also leaves it unchanged by SecondDeletionSlack plus
  deletion monotonicity.

Therefore, if the parent rays i->r and i->s are adjacent interior rays, the
three old quotient gaps surrounding them contain at least two zeros.
-/

namespace JSP000404Research

/-- Direct-cycle form of second-deletion exponent equality.  The theorem in
ConcreteSecondDeletionRigidity is phrased through deletedCycleFamily; here we
transport it back to the direct restrictDelete cycle at the chosen parent
survivor. -/
theorem direct_secondDeletion_exponent_eq_above_min
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane} {hp : Function.Injective p}
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
        ≤ 2 ^ n) :
    let hparent3 : 3 ≤ Fintype.card V := by omega
    let hotherR :=
      child_other_nonempty_of_card_ge_three hparent3 hir
    let child :=
      (C i).restrictDelete r hir hotherR
    let sChild : DeletedVertexType r :=
      childVertex r s hsr
    let iChild : DeletedVertexType r :=
      survivingCentre r i hir
    let hisChild : iChild ≠ sChild := by
      intro h
      apply his
      exact congrArg Subtype.val h
    let hchild3 : 3 ≤ Fintype.card (DeletedVertexType r) :=
      three_le_card_deletedVertexType r hcard
    let hotherS :=
      child_other_nonempty_of_card_ge_three hchild3 hisChild
    centreExponent
        (child.restrictDelete sChild hisChild hotherS) t
      =
    centreExponent child t := by
  dsimp
  let hparent3 : 3 ≤ Fintype.card V := by omega
  let childC := deletedCycleFamily C hparent3 r
  let sChild : DeletedVertexType r := childVertex r s hsr
  let iChild : DeletedVertexType r := childVertex r i hir
  have hisChild : iChild ≠ sChild := by
    intro h
    apply his
    exact congrArg Subtype.val h
  let hchild3 : 3 ≤ Fintype.card (DeletedVertexType r) :=
    three_le_card_deletedVertexType r hcard
  let hotherS :=
    child_other_nonempty_of_card_ge_three hchild3 hisChild
  have hEqFamily :=
    concrete_secondDeletion_exponent_eq_above_min
      C hcard ht n a r s i hsr hir his
      hsExp hiHigh hpostR hrigidR hgrand
  have hChildEq :
      childC iChild =
        (C i).restrictDelete r hir
          (child_other_nonempty_of_card_ge_three
            hparent3 hir) := by
    dsimp [childC, iChild]
    simpa [childVertex, survivingCentre] using
      deletedCycleFamily_at_survivingCentre_eq_restrictDelete
        C hparent3 r i hir
  simpa [childC, sChild, iChild, hchild3, hparent3,
    childVertex, survivingCentre, hChildEq]
    using hEqFamily

/-- Main high-survivor adjacent-ray rigidity theorem. -/
theorem adjacent_minimum_rays_at_high_survivor_force_sparse_triple
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane} (hp : Function.Injective p)
    (C : ∀ i : V, CentreProjectiveCycle hp i)
    (hcard : 4 ≤ Fintype.card V)
    {t : ℝ}
    (ht : 0 ≤ t)
    (n a : ℕ)
    (r s i : V)
    (hrs : r ≠ s)
    (hir : i ≠ r)
    (his : i ≠ s)
    (hrExp : centreExponent (C r) t = a)
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
        (childVertex r s hrs.symm)
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
  let hotherR :=
    child_other_nonempty_of_card_ge_three hparent3 hir
  let child :=
    (C i).restrictDelete r hir hotherR
  let sChild : DeletedVertexType r :=
    childVertex r s hrs.symm
  let iChild : DeletedVertexType r :=
    survivingCentre r i hir
  have hisChild : iChild ≠ sChild := by
    intro h
    apply his
    exact congrArg Subtype.val h
  let hchild3 : 3 ≤ Fintype.card (DeletedVertexType r) :=
    three_le_card_deletedVertexType r hcard
  let hotherS :=
    child_other_nonempty_of_card_ge_three hchild3 hisChild

  have hEq1Table :=
    hrigidR i hir
  have hEq1 :
      centreExponent child t =
        centreExponent (C i) t := by
    dsimp [child]
    rw [← concreteDeletionAfter_eq
      C hparent3 t hir]
    simpa [hparent3] using hEq1Table

  have hEq2 :
      centreExponent
          (child.restrictDelete sChild hisChild hotherS) t
        =
      centreExponent child t := by
    exact
      direct_secondDeletion_exponent_eq_above_min
        C hcard ht n a r s i hrs.symm hir his
        hsExp hiHigh
        (by simpa [hparent3] using hpostR)
        (by
          intro j hj
          simpa [hparent3] using hrigidR j hj)
        (by
          simpa [hparent3, hchild3] using hgrand)

  exact
    concrete_adjacent_double_deletion_triple_shape
      hp (C i) hir his hrs hotherR
      first mid tail next hrays ht hotherS hEq1 hEq2

#print axioms direct_secondDeletion_exponent_eq_above_min
#print axioms adjacent_minimum_rays_at_high_survivor_force_sparse_triple

end JSP000404Research
