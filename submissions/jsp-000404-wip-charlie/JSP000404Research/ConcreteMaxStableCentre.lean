
import JSP000404Research.ConcreteStableCentre
import JSP000404Research.MaxStableCentre
import JSP000404Research.TopTwoTailMultiplicity
import Mathlib.Tactic

/-!
# A concrete maximal stable centre in an uncompensated planar configuration

When the ambient finite configuration has at least three vertices, deleting
one vertex still leaves every other surviving centre with at least one other
vertex.  Hence CentreProjectiveCycle.restrictDelete is available uniformly.

This lets us package all genuine post-deletion centre exponents into one table

  concreteDeletionAfter C hcard t r i.

ConcreteCentreDeletionMonotone supplies survivor monotonicity for that table.
Therefore the abstract canonical unit-gain bonus / maximal-centre theorem
specializes directly to the actual planar projective cycles.

If no actual deletion preserves the old total dyadic mass, there exists a
maximal-exponent centre which is ConcreteDeletionUnitStable.
-/

namespace JSP000404Research

open scoped BigOperators

/-- After deleting r, a distinct survivor i still has another vertex whenever
the original finite set has at least three vertices. -/
theorem child_other_nonempty_of_card_ge_three
    {V : Type*} [Fintype V]
    (hcard : 3 ≤ Fintype.card V)
    {r i : V}
    (hir : i ≠ r) :
    Nonempty (OtherVertex (survivingCentre r i hir)) := by
  obtain ⟨j, hji, hjr⟩ :=
    exists_third_of_fintype_card_ge_three
      hcard hir
  let jChild : DeletedVertexType r := ⟨j, hjr⟩
  refine ⟨⟨jChild, ?_⟩⟩
  intro hEq
  apply hji
  exact congrArg Subtype.val hEq

/-- Uniform genuine post-deletion exponent table.  The diagonal value is
irrelevant because deletionPostWeight erases the deleted vertex itself. -/
noncomputable def concreteDeletionAfter
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane} {hp : Function.Injective p}
    (C : ∀ i : V, CentreProjectiveCycle hp i)
    (hcard : 3 ≤ Fintype.card V)
    (t : ℝ)
    (r i : V) : ℕ :=
  if hir : i ≠ r then
    centreExponent
      ((C i).restrictDelete r hir
        (child_other_nonempty_of_card_ge_three hcard hir)) t
  else
    0

theorem concreteDeletionAfter_eq
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane} {hp : Function.Injective p}
    (C : ∀ i : V, CentreProjectiveCycle hp i)
    (hcard : 3 ≤ Fintype.card V)
    (t : ℝ)
    {r i : V}
    (hir : i ≠ r) :
    concreteDeletionAfter C hcard t r i =
      centreExponent
        ((C i).restrictDelete r hir
          (child_other_nonempty_of_card_ge_three hcard hir)) t := by
  simp [concreteDeletionAfter, hir]

/-- Genuine survivor exponents never decrease. -/
theorem concreteDeletionAfter_mono
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane} {hp : Function.Injective p}
    (C : ∀ i : V, CentreProjectiveCycle hp i)
    (hcard : 3 ≤ Fintype.card V)
    {t : ℝ}
    (ht : 0 ≤ t)
    {r i : V}
    (hir : i ≠ r) :
    centreExponent (C i) t ≤
      concreteDeletionAfter C hcard t r i := by
  rw [concreteDeletionAfter_eq C hcard t hir]
  exact centreExponent_mono_restrictDelete
    (C i) hir
    (child_other_nonempty_of_card_ge_three hcard hir)
    ht

/-- The abstract no-unit-gain conclusion for the concrete post-deletion table
is exactly ConcreteDeletionUnitStable; proof arguments to Nonempty are
irrelevant. -/
theorem concreteStable_of_no_unit_gain_after
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane} {hp : Function.Injective p}
    (C : ∀ i : V, CentreProjectiveCycle hp i)
    (hcard : 3 ≤ Fintype.card V)
    (t : ℝ)
    {i : V}
    (hno :
      ∀ r : V, i ≠ r →
        ¬ centreExponent (C i) t + 1 ≤
          concreteDeletionAfter C hcard t r i) :
    ConcreteDeletionUnitStable (C i) t := by
  intro r hir hother
  have hcanon :=
    child_other_nonempty_of_card_ge_three hcard hir
  have hproof : hother = hcanon := Subsingleton.elim _ _
  subst hother
  rw [← concreteDeletionAfter_eq C hcard t hir]
  exact hno r hir

/-- Main concrete stable-max theorem.

If every genuine deletion has post-deletion mass strictly below the old mass,
then some maximal old exponent centre is deletion-stable under every incident
ray deletion.
-/
theorem exists_concrete_maximal_stable_of_no_compensated
    {V : Type*} [LinearOrder V] [Fintype V] [Nonempty V]
    {p : V → Plane} {hp : Function.Injective p}
    (C : ∀ i : V, CentreProjectiveCycle hp i)
    (hcard : 3 ≤ Fintype.card V)
    {t : ℝ}
    (ht : 0 ≤ t)
    (hnocomp :
      ∀ r : V,
        deletionPostWeight
            (concreteDeletionAfter C hcard t) r
          <
        ∑ i : V, 2 ^ centreExponent (C i) t) :
    ∃ i : V,
      (∀ j : V,
        centreExponent (C j) t ≤
          centreExponent (C i) t) ∧
      ConcreteDeletionUnitStable (C i) t := by
  let exponent : V → ℕ :=
    fun i => centreExponent (C i) t
  let after : V → V → ℕ :=
    concreteDeletionAfter C hcard t
  have hmono :
      ∀ r i, i ≠ r → exponent i ≤ after r i := by
    intro r i hir
    dsimp [exponent, after]
    exact concreteDeletionAfter_mono
      C hcard ht hir
  have hno' :
      ∀ r,
        deletionPostWeight after r <
          ∑ i : V, 2 ^ exponent i := by
    simpa [after, exponent] using hnocomp
  obtain ⟨i, hmax, hnogain⟩ :=
    exists_maximal_no_unit_gain_of_no_compensated
      exponent after hmono hno'
  refine ⟨i, ?_, ?_⟩
  · simpa [exponent] using hmax
  · apply concreteStable_of_no_unit_gain_after
      C hcard t
    intro r hir
    exact hnogain r hir

/-- Contrapositive form: if every maximal concrete centre has some unit-gain
incident deletion, then an actual compensated deletion exists. -/
theorem exists_concrete_compensated_of_every_max_unstable
    {V : Type*} [LinearOrder V] [Fintype V] [Nonempty V]
    {p : V → Plane} {hp : Function.Injective p}
    (C : ∀ i : V, CentreProjectiveCycle hp i)
    (hcard : 3 ≤ Fintype.card V)
    {t : ℝ}
    (ht : 0 ≤ t)
    (hunstable :
      ∀ i : V,
        (∀ j : V,
          centreExponent (C j) t ≤
            centreExponent (C i) t) →
        ¬ ConcreteDeletionUnitStable (C i) t) :
    ∃ r : V,
      (∑ i : V, 2 ^ centreExponent (C i) t) ≤
        deletionPostWeight
          (concreteDeletionAfter C hcard t) r := by
  by_contra hnone
  push_neg at hnone
  obtain ⟨i, hmax, hstable⟩ :=
    exists_concrete_maximal_stable_of_no_compensated
      C hcard ht hnone
  exact hunstable i hmax hstable

#print axioms child_other_nonempty_of_card_ge_three
#print axioms concreteDeletionAfter_mono
#print axioms exists_concrete_maximal_stable_of_no_compensated
#print axioms exists_concrete_compensated_of_every_max_unstable

end JSP000404Research
