
import JSP000404Research.ConcreteSecondDeletionBridge
import Mathlib.Tactic

/-!
# Concrete second-deletion rigidity inside the genuine first child

Let r be a first deleted minimum centre.  Assume its root deletion column is
rigid:

* post mass is exactly 2^n;
* every survivor keeps its old exponent.

Then the genuine child configuration indexed by DeletedVertexType r has total
dyadic mass exactly 2^n and inherits the parent exponent profile pointwise.

Now delete another surviving minimum centre s.  If this grandchild has dyadic
mass at most 2^n, SecondDeletionSlack applies literally to the child.

Consequently every survivor whose original exponent is strictly above the
minimum layer is unit-stable under the second deletion.  Among survivors still
in the minimum layer, at most one can acquire a full unit gain.
-/

namespace JSP000404Research

open scoped BigOperators

/-- Canonical child vertex corresponding to a parent survivor. -/
def childVertex
    {V : Type*}
    (r i : V) (hir : i ≠ r) :
    DeletedVertexType r :=
  ⟨i, hir⟩

/-- Concrete specialization of second-deletion rigidity above the minimum
layer. -/
theorem no_concrete_secondDeletion_unit_gain_above_min
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
    ¬
      centreExponent
          (deletedCycleFamily C (by omega) r
            (childVertex r i hir)) t + 1
        ≤
      concreteDeletionAfter
        (deletedCycleFamily C (by omega) r)
        (three_le_card_deletedVertexType r hcard)
        t
        (childVertex r s hsr)
        (childVertex r i hir) := by
  let hparent3 : 3 ≤ Fintype.card V := by omega
  let childC :=
    deletedCycleFamily C hparent3 r
  let hsChild : DeletedVertexType r :=
    childVertex r s hsr
  let hiChild : DeletedVertexType r :=
    childVertex r i hir
  let hchild3 :
      3 ≤ Fintype.card (DeletedVertexType r) :=
    three_le_card_deletedVertexType r hcard
  have htotal :
      (∑ j : DeletedVertexType r,
        2 ^ centreExponent (childC j) t)
        =
      2 ^ n := by
    simpa [childC, hparent3] using
      deletedCycleFamily_dyadicMass_eq_bound_of_root_column
        C hparent3 r t n
        (by simpa [hparent3] using hpostR)
  have hsChildExp :
      centreExponent (childC hsChild) t = a := by
    have h :=
      deletedCycleFamily_exponent_eq_parent_of_root_rigid
        C hparent3 r t
        (by
          intro j hj
          simpa [hparent3] using hrigidR j hj)
        hsChild
    simpa [childC, hsChild, childVertex, hsExp] using h
  have hiChildHigh :
      a < centreExponent (childC hiChild) t := by
    have h :=
      deletedCycleFamily_exponent_eq_parent_of_root_rigid
        C hparent3 r t
        (by
          intro j hj
          simpa [hparent3] using hrigidR j hj)
        hiChild
    simpa [childC, hiChild, childVertex] using
      (show a < centreExponent (C i) t from hiHigh)
  have hsiChild : hiChild ≠ hsChild := by
    intro hEq
    apply his
    exact congrArg Subtype.val hEq
  have hmonoChild :
      ∀ j : DeletedVertexType r,
        j ≠ hsChild →
        centreExponent (childC j) t ≤
          concreteDeletionAfter childC hchild3 t hsChild j := by
    intro j hjs
    exact concreteDeletionAfter_mono
      childC hchild3 ht hjs
  have hno :=
    no_secondDeletion_unit_gain_above_min
      (fun j : DeletedVertexType r =>
        centreExponent (childC j) t)
      (concreteDeletionAfter childC hchild3 t)
      n a hsChild hiChild
      htotal hsChildExp hmonoChild
      (by simpa [childC, hsChild, hchild3, hparent3]
          using hgrand)
      hsiChild hiChildHigh
  simpa [childC, hsChild, hiChild, hchild3, hparent3]
    using hno

/-- At most one other minimum-layer child survivor can gain a full unit when
the second minimum centre is deleted. -/
theorem no_two_concrete_secondDeletion_min_unit_gains
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane} {hp : Function.Injective p}
    (C : ∀ i : V, CentreProjectiveCycle hp i)
    (hcard : 4 ≤ Fintype.card V)
    {t : ℝ}
    (ht : 0 ≤ t)
    (n a : ℕ)
    (r s j k : V)
    (hsr : s ≠ r)
    (hjr : j ≠ r)
    (hkr : k ≠ r)
    (hjs : j ≠ s)
    (hks : k ≠ s)
    (hjk : j ≠ k)
    (hsExp : centreExponent (C s) t = a)
    (hjExp : centreExponent (C j) t = a)
    (hkExp : centreExponent (C k) t = a)
    (hpostR :
      deletionPostWeight
          (concreteDeletionAfter C (by omega) t) r
        = 2 ^ n)
    (hrigidR :
      ∀ x : V, x ≠ r →
        concreteDeletionAfter C (by omega) t r x =
          centreExponent (C x) t)
    (hgrand :
      deletionPostWeight
        (concreteDeletionAfter
          (deletedCycleFamily C (by omega) r)
          (three_le_card_deletedVertexType r hcard)
          t)
        (childVertex r s hsr)
        ≤ 2 ^ n) :
    ¬
      (
        centreExponent
            (deletedCycleFamily C (by omega) r
              (childVertex r j hjr)) t + 1
          ≤
        concreteDeletionAfter
          (deletedCycleFamily C (by omega) r)
          (three_le_card_deletedVertexType r hcard)
          t
          (childVertex r s hsr)
          (childVertex r j hjr)
        ∧
        centreExponent
            (deletedCycleFamily C (by omega) r
              (childVertex r k hkr)) t + 1
          ≤
        concreteDeletionAfter
          (deletedCycleFamily C (by omega) r)
          (three_le_card_deletedVertexType r hcard)
          t
          (childVertex r s hsr)
          (childVertex r k hkr)
      ) := by
  let hparent3 : 3 ≤ Fintype.card V := by omega
  let childC :=
    deletedCycleFamily C hparent3 r
  let hsChild : DeletedVertexType r :=
    childVertex r s hsr
  let hjChild : DeletedVertexType r :=
    childVertex r j hjr
  let hkChild : DeletedVertexType r :=
    childVertex r k hkr
  let hchild3 :
      3 ≤ Fintype.card (DeletedVertexType r) :=
    three_le_card_deletedVertexType r hcard
  have htotal :
      (∑ x : DeletedVertexType r,
        2 ^ centreExponent (childC x) t)
        =
      2 ^ n := by
    simpa [childC, hparent3] using
      deletedCycleFamily_dyadicMass_eq_bound_of_root_column
        C hparent3 r t n
        (by simpa [hparent3] using hpostR)
  have hchildEq :
      ∀ x : DeletedVertexType r,
        centreExponent (childC x) t =
          centreExponent (C x.1) t := by
    intro x
    exact
      deletedCycleFamily_exponent_eq_parent_of_root_rigid
        C hparent3 r t
        (by
          intro y hy
          simpa [hparent3] using hrigidR y hy)
        x
  have hsChildExp :
      centreExponent (childC hsChild) t = a := by
    rw [hchildEq hsChild]
    exact hsExp
  have hjChildExp :
      centreExponent (childC hjChild) t = a := by
    rw [hchildEq hjChild]
    exact hjExp
  have hkChildExp :
      centreExponent (childC hkChild) t = a := by
    rw [hchildEq hkChild]
    exact hkExp
  have hsj : hjChild ≠ hsChild := by
    intro hEq
    apply hjs
    exact congrArg Subtype.val hEq
  have hsk : hkChild ≠ hsChild := by
    intro hEq
    apply hks
    exact congrArg Subtype.val hEq
  have hjkChild : hjChild ≠ hkChild := by
    intro hEq
    apply hjk
    exact congrArg Subtype.val hEq
  have hmonoChild :
      ∀ x : DeletedVertexType r,
        x ≠ hsChild →
        centreExponent (childC x) t ≤
          concreteDeletionAfter childC hchild3 t hsChild x := by
    intro x hxs
    exact concreteDeletionAfter_mono
      childC hchild3 ht hxs
  have hno :=
    no_two_secondDeletion_min_unit_gains
      (fun x : DeletedVertexType r =>
        centreExponent (childC x) t)
      (concreteDeletionAfter childC hchild3 t)
      n a hsChild hjChild hkChild
      htotal hsChildExp hmonoChild
      (by simpa [childC, hsChild, hchild3, hparent3]
          using hgrand)
      hsj hsk hjkChild hjChildExp hkChildExp
  simpa [childC, hsChild, hjChild, hkChild,
    hchild3, hparent3] using hno


/-- Geometric form of the high-survivor second-deletion rigidity: in the first
child, the ray to the second deleted minimum centre has a zero quotient on at
least one cyclic side. -/
theorem second_minimum_deleted_ray_adjacent_zero_at_high_survivor
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
    let childC :=
      deletedCycleFamily C (by omega : 3 ≤ Fintype.card V) r
    let sChild := childVertex r s hsr
    let iChild := childVertex r i hir
    ∃ pre post : List (OtherVertex iChild),
      (childC iChild).rays =
        pre ++
          deletedParentRay sChild iChild
            (by
              intro h
              apply his
              exact congrArg Subtype.val h) ::
          post
      ∧
      match pre, post with
      | [], [] => True
      | [], b :: bs =>
          Nat.floor
            (t * ((rayThetaAt
                (restrictedPoint_injective hp r) iChild b -
              rayThetaAt
                (restrictedPoint_injective hp r) iChild
                (deletedParentRay sChild iChild
                  (by
                    intro h
                    apply his
                    exact congrArg Subtype.val h))) /
                Real.pi)) = 0
          ∨
          Nat.floor
            (t * ((rayThetaAt
                (restrictedPoint_injective hp r) iChild
                (deletedParentRay sChild iChild
                  (by
                    intro h
                    apply his
                    exact congrArg Subtype.val h)) +
              Real.pi -
              (bs.map
                (rayThetaAt
                  (restrictedPoint_injective hp r)
                  iChild)).getLastD
                (rayThetaAt
                  (restrictedPoint_injective hp r)
                  iChild b)) / Real.pi)) = 0
      | first :: mid, [] =>
          Nat.floor
            (t * ((rayThetaAt
                (restrictedPoint_injective hp r) iChild
                (deletedParentRay sChild iChild
                  (by
                    intro h
                    apply his
                    exact congrArg Subtype.val h)) -
              (mid.map
                (rayThetaAt
                  (restrictedPoint_injective hp r)
                  iChild)).getLastD
                (rayThetaAt
                  (restrictedPoint_injective hp r)
                  iChild first)) / Real.pi)) = 0
          ∨
          Nat.floor
            (t * ((rayThetaAt
                (restrictedPoint_injective hp r) iChild first +
              Real.pi -
              rayThetaAt
                (restrictedPoint_injective hp r) iChild
                (deletedParentRay sChild iChild
                  (by
                    intro h
                    apply his
                    exact congrArg Subtype.val h))) /
                Real.pi)) = 0
      | first :: mid, next :: tail =>
          Nat.floor
            (t * ((rayThetaAt
                (restrictedPoint_injective hp r) iChild
                (deletedParentRay sChild iChild
                  (by
                    intro h
                    apply his
                    exact congrArg Subtype.val h)) -
              (mid.map
                (rayThetaAt
                  (restrictedPoint_injective hp r)
                  iChild)).getLastD
                (rayThetaAt
                  (restrictedPoint_injective hp r)
                  iChild first)) / Real.pi)) = 0
          ∨
          Nat.floor
            (t * ((rayThetaAt
                (restrictedPoint_injective hp r) iChild next -
              rayThetaAt
                (restrictedPoint_injective hp r) iChild
                (deletedParentRay sChild iChild
                  (by
                    intro h
                    apply his
                    exact congrArg Subtype.val h))) /
                Real.pi)) = 0 := by
  let hparent3 : 3 ≤ Fintype.card V := by omega
  let childC :=
    deletedCycleFamily C hparent3 r
  let sChild : DeletedVertexType r :=
    childVertex r s hsr
  let iChild : DeletedVertexType r :=
    childVertex r i hir
  let hchild3 :
      3 ≤ Fintype.card (DeletedVertexType r) :=
    three_le_card_deletedVertexType r hcard
  have hisChild : iChild ≠ sChild := by
    intro h
    apply his
    exact congrArg Subtype.val h
  let hother :=
    child_other_nonempty_of_card_ge_three
      hchild3 hisChild
  obtain ⟨pre, post, hsplit⟩ :=
    exists_parent_cycle_split_at_deleted
      (childC iChild) sChild hisChild
  refine ⟨pre, post, hsplit, ?_⟩
  have hnoTable :
      ¬
        centreExponent (childC iChild) t + 1
          ≤
        concreteDeletionAfter
          childC hchild3 t sChild iChild := by
    exact no_concrete_secondDeletion_unit_gain_above_min
      C hcard ht n a r s i hsr hir his
      hsExp hiHigh hpostR hrigidR hgrand
  have hno :
      ¬
        centreExponent (childC iChild) t + 1
          ≤
        centreExponent
          ((childC iChild).restrictDelete
            sChild hisChild hother) t := by
    rw [← concreteDeletionAfter_eq
      childC hchild3 t hisChild]
    exact hnoTable
  exact adjacent_zero_of_no_unit_gain
    (childC iChild) hisChild hother
    pre post hsplit ht hno

#print axioms second_minimum_deleted_ray_adjacent_zero_at_high_survivor

#print axioms no_concrete_secondDeletion_unit_gain_above_min
#print axioms no_two_concrete_secondDeletion_min_unit_gains

end JSP000404Research
