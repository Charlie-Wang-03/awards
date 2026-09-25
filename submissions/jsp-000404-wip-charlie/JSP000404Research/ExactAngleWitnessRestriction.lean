
import JSP000404Research.SharpCentre
import Mathlib.Tactic

/-!
# Exact angle-cap witnesses survive deletion away from the witness triple

AngleCap only records the upper bound

  angle <= pi-lambda.

For exact-normalization induction we additionally need one triple attaining the
cap.  This file packages that information as ExactAngleCap.

If r is not one of the three vertices of a chosen exact witness, deleting r
preserves both:

* the same uniform AngleCap at lambda;
* the same equality witness angle = pi-lambda.

Hence the child configuration has the same exact normalization parameter
lambda (and therefore the same t=pi/lambda) whenever the deleted vertex lies
outside one maximizing-angle witness triple.
-/

namespace JSP000404Research

/-- A concrete ordered witness for equality in the uniform angle cap.  The
middle vertex b is the angle centre. -/
structure ExactAngleWitness
    {V : Type*}
    (p : V → Plane)
    (lam : ℝ) where
  a : V
  b : V
  c : V
  hab : a ≠ b
  hac : a ≠ c
  hbc : b ≠ c
  exact :
    EuclideanGeometry.angle (p a) (p b) (p c) =
      Real.pi - lam

/-- Exact angle cap: global upper bound plus at least one attaining triple. -/
def ExactAngleCap
    {V : Type*}
    (p : V → Plane)
    (lam : ℝ) : Prop :=
  AngleCap p lam ∧ Nonempty (ExactAngleWitness p lam)

/-- Vertex-deleted subtype. -/
abbrev DeletedVertex
    {V : Type*}
    (r : V) :=
  {v : V // v ≠ r}

def deletePoint
    {V : Type*}
    (p : V → Plane)
    (r : V) :
    DeletedVertex r → Plane :=
  fun v => p v.1

theorem deletePoint_injective
    {V : Type*}
    {p : V → Plane}
    (hp : Function.Injective p)
    (r : V) :
    Function.Injective (deletePoint p r) := by
  intro u v huv
  apply Subtype.ext
  exact hp huv

/-- Any angle cap restricts to a vertex-deleted subconfiguration. -/
theorem angleCap_deletePoint
    {V : Type*}
    {p : V → Plane}
    {lam : ℝ}
    (hcap : AngleCap p lam)
    (r : V) :
    AngleCap (deletePoint p r) lam := by
  intro a b c hab hac hbc
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

/-- A specified exact witness survives deletion of a vertex outside the
witness triple. -/
def ExactAngleWitness.delete
    {V : Type*}
    {p : V → Plane}
    {lam : ℝ}
    (W : ExactAngleWitness p lam)
    (r : V)
    (hra : r ≠ W.a)
    (hrb : r ≠ W.b)
    (hrc : r ≠ W.c) :
    ExactAngleWitness (deletePoint p r) lam where
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
    simpa [deletePoint] using W.exact

/-- Exact normalization is inherited by deleting any vertex outside one fixed
attaining triple. -/
theorem exactAngleCap_deletePoint_of_avoids_witness
    {V : Type*}
    {p : V → Plane}
    {lam : ℝ}
    (hcap : AngleCap p lam)
    (W : ExactAngleWitness p lam)
    (r : V)
    (hra : r ≠ W.a)
    (hrb : r ≠ W.b)
    (hrc : r ≠ W.c) :
    ExactAngleCap (deletePoint p r) lam := by
  constructor
  · exact angleCap_deletePoint hcap r
  · exact ⟨W.delete r hra hrb hrc⟩

/-- Existential form: if an exact configuration has a witness avoiding r,
then its deletion remains exact at the same lambda. -/
theorem exactAngleCap_deletePoint
    {V : Type*}
    {p : V → Plane}
    {lam : ℝ}
    (hexact : ExactAngleCap p lam)
    (r : V)
    (havoid :
      ∃ W : ExactAngleWitness p lam,
        r ≠ W.a ∧ r ≠ W.b ∧ r ≠ W.c) :
    ExactAngleCap (deletePoint p r) lam := by
  obtain ⟨W, hra, hrb, hrc⟩ := havoid
  exact exactAngleCap_deletePoint_of_avoids_witness
    hexact.1 W r hra hrb hrc

/-- The original exact witness provides the converse numerical statement:
lambda really is pi minus the attained angle. -/
theorem ExactAngleWitness.lam_eq_pi_sub_angle
    {V : Type*}
    {p : V → Plane}
    {lam : ℝ}
    (W : ExactAngleWitness p lam) :
    lam =
      Real.pi -
        EuclideanGeometry.angle (p W.a) (p W.b) (p W.c) := by
  linarith [W.exact]

#print axioms angleCap_deletePoint
#print axioms ExactAngleWitness.delete
#print axioms exactAngleCap_deletePoint_of_avoids_witness
#print axioms exactAngleCap_deletePoint

end JSP000404Research
