import JSP000404Research.ConcreteDoubleDeletionRestriction
import JSP000404Research.InteriorDoubleDeletionRigidity
import Mathlib.Tactic

/-!
# Concrete adjacent double-deletion rigidity

This file reconnects the list theorem InteriorDoubleDeletionRigidity to an
actual CentreProjectiveCycle.

Assume that, at a survivor i, the parent sorted ray list contains two adjacent
interior rays to r and s,

  first :: (mid ++ ray(r) :: ray(s) :: next :: tail).

Delete r and then s.  If the centre exponent at i is unchanged in both
deletions, then among the three parent quotients immediately surrounding the
two deleted rays at least two are zero.

Thus two adjacent zero-gain deletion columns force a genuine three-gap sparse
shape in the original planar centre cycle.
-/

namespace JSP000404Research

open Real

theorem concrete_adjacent_double_deletion_triple_shape
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane} (hp : Function.Injective p)
    {i r s : V}
    (C : CentreProjectiveCycle hp i)
    (hir : i ≠ r)
    (his : i ≠ s)
    (hrs : r ≠ s)
    (hotherR :
      Nonempty (OtherVertex (survivingCentre r i hir)))
    (first : OtherVertex i)
    (mid tail : List (OtherVertex i))
    (next : OtherVertex i)
    (hrays :
      C.rays =
        first ::
          (mid ++
            deletedParentRay r i hir ::
            deletedParentRay s i his ::
            next :: tail))
    {t : ℝ}
    (ht : 0 ≤ t)
    (hotherS :
      let sChild : DeletedVertexType r :=
        childVertex r s hrs.symm
      let iChild : DeletedVertexType r :=
        survivingCentre r i hir
      let hiChild : iChild ≠ sChild := by
        intro h
        apply his
        exact congrArg Subtype.val h
      Nonempty
        (OtherVertex
          (survivingCentre sChild iChild hiChild)))
    (hEq1 :
      centreExponent
          (C.restrictDelete r hir hotherR) t
        =
      centreExponent C t)
    (hEq2 :
      let sChild : DeletedVertexType r :=
        childVertex r s hrs.symm
      let iChild : DeletedVertexType r :=
        survivingCentre r i hir
      let hiChild : iChild ≠ sChild := by
        intro h
        apply his
        exact congrArg Subtype.val h
      let child := C.restrictDelete r hir hotherR
      centreExponent
          (child.restrictDelete sChild hiChild hotherS) t
        =
      centreExponent child t) :
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
  dsimp
  let theta := rayThetaAt hp i
  let a := theta first
  let pre := mid.map theta
  let x := theta (deletedParentRay r i hir)
  let y := theta (deletedParentRay s i his)
  let z := theta next
  let tailA := tail.map theta
  let child := C.restrictDelete r hir hotherR
  let sChild : DeletedVertexType r :=
    childVertex r s hrs.symm
  let iChild : DeletedVertexType r :=
    survivingCentre r i hir
  have hiChild : iChild ≠ sChild := by
    intro h
    apply his
    exact congrArg Subtype.val h
  let grand :=
    child.restrictDelete sChild hiChild hotherS

  have hParentAngles :
      C.angles =
        a :: (pre ++ x :: y :: z :: tailA) := by
    simp [CentreProjectiveCycle.angles, hrays,
      theta, a, pre, x, y, z, tailA,
      List.map_append, List.append_assoc]

  have hsplitAdj :
      C.rays =
        (first :: mid) ++
          deletedParentRay r i hir ::
          deletedParentRay s i his ::
          (next :: tail) := by
    simpa [List.append_assoc] using hrays

  have hsplitR :
      C.rays =
        (first :: mid) ++
          deletedParentRay r i hir ::
          (deletedParentRay s i his :: next :: tail) := by
    simpa [List.append_assoc] using hsplitAdj

  have hChildAngles0 :=
    restrictDelete_angles_of_parent_split
      C r hir hotherR
      (first :: mid)
      (deletedParentRay s i his :: next :: tail)
      hsplitR
  have hChildAngles :
      child.angles =
        a :: (pre ++ y :: z :: tailA) := by
    dsimp [child] at hChildAngles0
    simpa [theta, a, pre, y, z, tailA,
      List.map_append, List.append_assoc] using hChildAngles0

  have hGrandAngles0 :=
    restrictDelete_twice_angles_of_adjacent_parent_split
      hp C hir his hrs hotherR
      (first :: mid) (next :: tail)
      hsplitAdj hotherS
  have hGrandAngles :
      grand.angles =
        a :: (pre ++ z :: tailA) := by
    dsimp [grand, child, sChild, iChild] at hGrandAngles0
    simpa [theta, a, pre, z, tailA,
      List.map_append, List.append_assoc] using hGrandAngles0

  have hParentGaps :
      C.gaps =
        normalizedProjectiveGaps
          (a :: (pre ++ x :: y :: z :: tailA)) := by
    unfold CentreProjectiveCycle.gaps
    rw [hParentAngles]

  have hChildGaps :
      child.gaps =
        normalizedProjectiveGaps
          (a :: (pre ++ y :: z :: tailA)) := by
    unfold CentreProjectiveCycle.gaps
    rw [hChildAngles]

  have hGrandGaps :
      grand.gaps =
        normalizedProjectiveGaps
          (a :: (pre ++ z :: tailA)) := by
    unfold CentreProjectiveCycle.gaps
    rw [hGrandAngles]

  have hg0 :
      0 ≤ (x - pre.getLastD a) / Real.pi := by
    apply C.gaps_nonneg
    rw [hParentGaps,
      normalizedProjectiveGaps_interior_parent
        a pre x y (z :: tailA)]
    simp
  have hg1 :
      0 ≤ (y - x) / Real.pi := by
    apply C.gaps_nonneg
    rw [hParentGaps,
      normalizedProjectiveGaps_interior_parent
        a pre x y (z :: tailA)]
    simp
  have hg2 :
      0 ≤ (z - y) / Real.pi := by
    apply C.gaps_nonneg
    rw [hParentGaps,
      normalizedProjectiveGaps_interior_parent
        a pre x y (z :: tailA)]
    simp [normalizedSuffixGaps, successiveDiffsFrom]

  have hEqList1 :
      listExponent
          (quotientList t
            (normalizedProjectiveGaps
              (a :: (pre ++ y :: z :: tailA))))
        =
      listExponent
          (quotientList t
            (normalizedProjectiveGaps
              (a :: (pre ++ x :: y :: z :: tailA)))) := by
    calc
      listExponent
          (quotientList t
            (normalizedProjectiveGaps
              (a :: (pre ++ y :: z :: tailA))))
          =
        listExponent (quotientList t child.gaps) := by
          rw [hChildGaps]
      _ = centreExponent child t :=
        listExponent_quotientList_eq_centreExponent' child t
      _ = centreExponent C t := by
        simpa [child] using hEq1
      _ = listExponent (quotientList t C.gaps) :=
        (listExponent_quotientList_eq_centreExponent' C t).symm
      _ =
        listExponent
          (quotientList t
            (normalizedProjectiveGaps
              (a :: (pre ++ x :: y :: z :: tailA)))) := by
          rw [hParentGaps]

  have hEqList2 :
      listExponent
          (quotientList t
            (normalizedProjectiveGaps
              (a :: (pre ++ z :: tailA))))
        =
      listExponent
          (quotientList t
            (normalizedProjectiveGaps
              (a :: (pre ++ y :: z :: tailA)))) := by
    calc
      listExponent
          (quotientList t
            (normalizedProjectiveGaps
              (a :: (pre ++ z :: tailA))))
          =
        listExponent (quotientList t grand.gaps) := by
          rw [hGrandGaps]
      _ = centreExponent grand t :=
        listExponent_quotientList_eq_centreExponent' grand t
      _ = centreExponent child t := by
        simpa [grand, child, sChild, iChild] using hEq2
      _ = listExponent (quotientList t child.gaps) :=
        (listExponent_quotientList_eq_centreExponent' child t).symm
      _ =
        listExponent
          (quotientList t
            (normalizedProjectiveGaps
              (a :: (pre ++ y :: z :: tailA)))) := by
          rw [hChildGaps]

  exact
    interior_double_deletion_triple_shape
      ht hg0 hg1 hg2 hEqList1 hEqList2

#print axioms concrete_adjacent_double_deletion_triple_shape

end JSP000404Research
