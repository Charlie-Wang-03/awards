
import JSP000404Research.ExactAngleWitnessRestriction
import JSP000404Research.ConcreteSecondDeletionRigidity
import Mathlib.Tactic

/-!
# Exact normalization survives two witness-avoiding deletions

The first deletion already has two parallel point-function names in the
research tree:

* deletePoint, used by ExactAngleWitnessRestriction;
* restrictedPoint, used by the concrete centre-cycle restriction machinery.

They are definitionally the same map.

This file gives the direct restrictedPoint witness constructor and then
iterates it once.  If r and s both avoid one fixed attaining angle witness
W=(a,b,c), and r!=s, then deleting r and subsequently deleting the child
vertex corresponding to s preserves the exact same lambda.

Hence a cardinality induction hypothesis for exact-normalized configurations
may be applied to the genuine second-deletion grandchild at the unchanged
Sendov scale t=pi/lambda.
-/

namespace JSP000404Research

/-- Restrict one exact witness using the point-function employed by the
centre-cycle deletion machinery. -/
def ExactAngleWitness.restrictPoint
    {V : Type*}
    {p : V → Plane}
    {lam : ℝ}
    (W : ExactAngleWitness p lam)
    (r : V)
    (hra : r ≠ W.a)
    (hrb : r ≠ W.b)
    (hrc : r ≠ W.c) :
    ExactAngleWitness (restrictedPoint p r) lam where
  a := ⟨W.a, Ne.symm hra⟩
  b := ⟨W.b, Ne.symm hrb⟩
  c := ⟨W.c, Ne.symm hrc⟩
  hab := by
    intro h
    apply W.hab
    exact congrArg Subtype.val h
  hac := by
    intro h
    apply W.hac
    exact congrArg Subtype.val h
  hbc := by
    intro h
    apply W.hbc
    exact congrArg Subtype.val h
  exact := by
    simpa [restrictedPoint] using W.exact

@[simp] theorem ExactAngleWitness.restrictPoint_a_val
    {V : Type*}
    {p : V → Plane}
    {lam : ℝ}
    (W : ExactAngleWitness p lam)
    (r : V)
    (hra : r ≠ W.a)
    (hrb : r ≠ W.b)
    (hrc : r ≠ W.c) :
    (W.restrictPoint r hra hrb hrc).a.1 = W.a := rfl

@[simp] theorem ExactAngleWitness.restrictPoint_b_val
    {V : Type*}
    {p : V → Plane}
    {lam : ℝ}
    (W : ExactAngleWitness p lam)
    (r : V)
    (hra : r ≠ W.a)
    (hrb : r ≠ W.b)
    (hrc : r ≠ W.c) :
    (W.restrictPoint r hra hrb hrc).b.1 = W.b := rfl

@[simp] theorem ExactAngleWitness.restrictPoint_c_val
    {V : Type*}
    {p : V → Plane}
    {lam : ℝ}
    (W : ExactAngleWitness p lam)
    (r : V)
    (hra : r ≠ W.a)
    (hrb : r ≠ W.b)
    (hrc : r ≠ W.c) :
    (W.restrictPoint r hra hrb hrc).c.1 = W.c := rfl

/-- One witness-avoiding restriction preserves ExactAngleCap in the concrete
restrictedPoint representation. -/
theorem exactAngleCap_restrictedPoint_of_avoids_witness
    {V : Type*}
    {p : V → Plane}
    {lam : ℝ}
    (hcap : AngleCap p lam)
    (W : ExactAngleWitness p lam)
    (r : V)
    (hra : r ≠ W.a)
    (hrb : r ≠ W.b)
    (hrc : r ≠ W.c) :
    ExactAngleCap (restrictedPoint p r) lam := by
  constructor
  · intro a b c hab hac hbc
    exact hcap a.1 b.1 c.1
      (by
        intro h
        apply hab
        exact Subtype.ext h)
      (by
        intro h
        apply hac
        exact Subtype.ext h)
      (by
        intro h
        apply hbc
        exact Subtype.ext h)
  · exact ⟨W.restrictPoint r hra hrb hrc⟩

/-- The parent survivor s as a child vertex is distinct from every surviving
witness vertex whenever s avoided that parent witness vertex. -/
theorem childVertex_ne_restrictedWitness_a
    {V : Type*}
    {p : V → Plane}
    {lam : ℝ}
    (W : ExactAngleWitness p lam)
    {r s : V}
    (hsr : s ≠ r)
    (hra : r ≠ W.a)
    (hrb : r ≠ W.b)
    (hrc : r ≠ W.c)
    (hsa : s ≠ W.a) :
    childVertex r s hsr ≠
      (W.restrictPoint r hra hrb hrc).a := by
  intro h
  apply hsa
  exact congrArg Subtype.val h

theorem childVertex_ne_restrictedWitness_b
    {V : Type*}
    {p : V → Plane}
    {lam : ℝ}
    (W : ExactAngleWitness p lam)
    {r s : V}
    (hsr : s ≠ r)
    (hra : r ≠ W.a)
    (hrb : r ≠ W.b)
    (hrc : r ≠ W.c)
    (hsb : s ≠ W.b) :
    childVertex r s hsr ≠
      (W.restrictPoint r hra hrb hrc).b := by
  intro h
  apply hsb
  exact congrArg Subtype.val h

theorem childVertex_ne_restrictedWitness_c
    {V : Type*}
    {p : V → Plane}
    {lam : ℝ}
    (W : ExactAngleWitness p lam)
    {r s : V}
    (hsr : s ≠ r)
    (hra : r ≠ W.a)
    (hrb : r ≠ W.b)
    (hrc : r ≠ W.c)
    (hsc : s ≠ W.c) :
    childVertex r s hsr ≠
      (W.restrictPoint r hra hrb hrc).c := by
  intro h
  apply hsc
  exact congrArg Subtype.val h

/-- Main two-deletion exact-normalization theorem. -/
theorem exactAngleCap_restrictedPoint_twice
    {V : Type*}
    {p : V → Plane}
    {lam : ℝ}
    (hcap : AngleCap p lam)
    (W : ExactAngleWitness p lam)
    {r s : V}
    (hrs : r ≠ s)
    (hra : r ≠ W.a)
    (hrb : r ≠ W.b)
    (hrc : r ≠ W.c)
    (hsa : s ≠ W.a)
    (hsb : s ≠ W.b)
    (hsc : s ≠ W.c) :
    ExactAngleCap
      (restrictedPoint
        (restrictedPoint p r)
        (childVertex r s hrs.symm))
      lam := by
  let W1 :=
    W.restrictPoint r hra hrb hrc
  let s1 : DeletedVertexType r :=
    childVertex r s hrs.symm
  have hcap1 :
      AngleCap (restrictedPoint p r) lam :=
    (exactAngleCap_restrictedPoint_of_avoids_witness
      hcap W r hra hrb hrc).1
  have hsa1 : s1 ≠ W1.a := by
    exact childVertex_ne_restrictedWitness_a
      W hrs.symm hra hrb hrc hsa
  have hsb1 : s1 ≠ W1.b := by
    exact childVertex_ne_restrictedWitness_b
      W hrs.symm hra hrb hrc hsb
  have hsc1 : s1 ≠ W1.c := by
    exact childVertex_ne_restrictedWitness_c
      W hrs.symm hra hrb hrc hsc
  exact exactAngleCap_restrictedPoint_of_avoids_witness
    hcap1 W1 s1 hsa1 hsb1 hsc1

/-- Two deletions reduce finite cardinality by exactly two. -/
theorem card_doubleDeletedVertexType
    {V : Type*} [Fintype V]
    (r : V)
    (s : DeletedVertexType r) :
    Fintype.card (DeletedVertexType s) =
      Fintype.card V - 2 := by
  rw [card_deletedVertexType s,
      card_deletedVertexType r]
  omega

/-- A parent with at least five vertices leaves at least three after two
deletions, enough for the concrete centre-cycle machinery to continue. -/
theorem three_le_card_doubleDeletedVertexType
    {V : Type*} [Fintype V]
    (r : V)
    (s : DeletedVertexType r)
    (hcard : 5 ≤ Fintype.card V) :
    3 ≤ Fintype.card (DeletedVertexType s) := by
  rw [card_doubleDeletedVertexType r s]
  omega

#print axioms ExactAngleWitness.restrictPoint
#print axioms exactAngleCap_restrictedPoint_of_avoids_witness
#print axioms exactAngleCap_restrictedPoint_twice
#print axioms card_doubleDeletedVertexType
#print axioms three_le_card_doubleDeletedVertexType

end JSP000404Research
