import JSP000404Research.FiniteProjectiveRays
import Mathlib.Tactic

/-!
# Canonical projective rays commute with deleting another vertex

Fix a finite injective planar configuration p : V -> Plane and delete one
vertex r.  The restricted configuration is indexed by

  {v : V // v != r}.

For a surviving centre i!=r, every non-centre child vertex corresponds
canonically to one parent non-centre vertex different from r.

Because the displacement vector itself is literally unchanged by restriction,
the canonical projective ray data rho, sigma and theta are unchanged as well.

This is the type-theoretic geometric half needed to lift the general cyclic
gap-deletion arithmetic to actual centre exponents.
-/

namespace JSP000404Research

abbrev DeletedVertexType
    {V : Type*} (r : V) :=
  {v : V // v ≠ r}

def restrictedPoint
    {V : Type*} (p : V → Plane) (r : V) :
    DeletedVertexType r → Plane :=
  fun v => p v.1

theorem restrictedPoint_injective
    {V : Type*} {p : V → Plane}
    (hp : Function.Injective p)
    (r : V) :
    Function.Injective (restrictedPoint p r) := by
  intro a b hab
  apply Subtype.ext
  exact hp hab

/-- A surviving centre as a vertex of the deleted configuration. -/
def survivingCentre
    {V : Type*} (r i : V) (hir : i ≠ r) :
    DeletedVertexType r :=
  ⟨i, hir⟩

/-- Map a child non-centre vertex back to the corresponding parent
non-centre vertex. -/
def childOtherToParent
    {V : Type*}
    (r i : V) (hir : i ≠ r) :
    OtherVertex (survivingCentre r i hir) →
      OtherVertex i :=
  fun j =>
    ⟨j.1.1, by
      intro hji
      apply j.2
      apply Subtype.ext
      exact hji⟩

/-- The parent image of a child ray is never the deleted ray. -/
theorem childOtherToParent_ne_deleted
    {V : Type*}
    (r i : V) (hir : i ≠ r)
    (j : OtherVertex (survivingCentre r i hir)) :
    (childOtherToParent r i hir j).1 ≠ r :=
  j.1.2

/-- Parent rays which survive deletion. -/
abbrev ParentSurvivorRay
    {V : Type*}
    (r i : V) :=
  {j : OtherVertex i // j.1 ≠ r}

/-- Child non-centre vertices are exactly the parent rays except the deleted
one. -/
def childOtherEquivParentSurvivor
    {V : Type*}
    (r i : V) (hir : i ≠ r) :
    OtherVertex (survivingCentre r i hir) ≃
      ParentSurvivorRay r i where
  toFun j :=
    ⟨childOtherToParent r i hir j,
      childOtherToParent_ne_deleted r i hir j⟩
  invFun j :=
    ⟨⟨j.1.1, j.2⟩, by
      intro h
      apply j.1.2
      exact congrArg Subtype.val h⟩
  left_inv j := by
    apply Subtype.ext
    rfl
  right_inv j := by
    apply Subtype.ext
    apply Subtype.ext
    rfl

@[simp] theorem childOtherEquivParentSurvivor_val
    {V : Type*}
    (r i : V) (hir : i ≠ r)
    (j : OtherVertex (survivingCentre r i hir)) :
    ((childOtherEquivParentSurvivor r i hir j).1).1 =
      j.1.1 := rfl

/-- The restricted displacement vector is literally the parent displacement. -/
theorem restricted_displacement_eq_parent
    {V : Type*} {p : V → Plane}
    (r i : V) (hir : i ≠ r)
    (j : OtherVertex (survivingCentre r i hir)) :
    restrictedPoint p r j.1 -
        restrictedPoint p r (survivingCentre r i hir)
      =
    p (childOtherToParent r i hir j).1 - p i := by
  rfl

/-- Canonical ray rho is invariant under deletion of another vertex. -/
theorem rayRhoAt_restrict_delete
    {V : Type*} {p : V → Plane}
    (hp : Function.Injective p)
    (r i : V) (hir : i ≠ r)
    (j : OtherVertex (survivingCentre r i hir)) :
    rayRhoAt
        (restrictedPoint_injective hp r)
        (survivingCentre r i hir) j
      =
    rayRhoAt hp i (childOtherToParent r i hir j) := by
  rfl

/-- Canonical ray sign is invariant under deletion of another vertex. -/
theorem raySignAt_restrict_delete
    {V : Type*} {p : V → Plane}
    (hp : Function.Injective p)
    (r i : V) (hir : i ≠ r)
    (j : OtherVertex (survivingCentre r i hir)) :
    raySignAt
        (restrictedPoint_injective hp r)
        (survivingCentre r i hir) j
      =
    raySignAt hp i (childOtherToParent r i hir j) := by
  rfl

/-- Canonical projective theta is invariant under deletion of another vertex. -/
theorem rayThetaAt_restrict_delete
    {V : Type*} {p : V → Plane}
    (hp : Function.Injective p)
    (r i : V) (hir : i ≠ r)
    (j : OtherVertex (survivingCentre r i hir)) :
    rayThetaAt
        (restrictedPoint_injective hp r)
        (survivingCentre r i hir) j
      =
    rayThetaAt hp i (childOtherToParent r i hir j) := by
  rfl

/-- Full canonical projective representation is invariant as a structure. -/
theorem rayRepAt_restrict_delete
    {V : Type*} {p : V → Plane}
    (hp : Function.Injective p)
    (r i : V) (hir : i ≠ r)
    (j : OtherVertex (survivingCentre r i hir)) :
    rayRepAt
        (restrictedPoint_injective hp r)
        (survivingCentre r i hir) j
      =
    rayRepAt hp i (childOtherToParent r i hir j) := by
  rfl

#print axioms restrictedPoint_injective
#print axioms childOtherEquivParentSurvivor
#print axioms restricted_displacement_eq_parent
#print axioms rayRhoAt_restrict_delete
#print axioms raySignAt_restrict_delete
#print axioms rayThetaAt_restrict_delete
#print axioms rayRepAt_restrict_delete

end JSP000404Research
