
import JSP000404Research.ConcreteMaxStableCentre
import Mathlib.Tactic

/-!
# Overweight minimal counterexamples contain a maximal concrete stable centre

ConcreteMaxStableCentre proves that if no actual vertex deletion is
compensated, then a maximal-exponent centre is deletion-unit-stable.

In an induction step all completed (s-1)-centre deletions are already bounded
by the target B.  Therefore an overweight configuration W>B cannot have a
compensated deletion: such a deletion would give

  W <= post(r) <= B,

a contradiction.

Hence every overweight minimal counterexample contains a centre i which is

* maximal for the old Sendov exponent, and
* ConcreteDeletionUnitStable.

This file packages that reduction so the remaining geometry can work only
with the maximal stable centre and forget the global deletion table.
-/

namespace JSP000404Research

open scoped BigOperators

/-- Unconditional dichotomy for actual centre cycles: either one genuine
deletion is compensated, or a maximal old-exponent centre is concrete-stable. -/
theorem concrete_compensated_or_maximal_stable
    {V : Type*} [LinearOrder V] [Fintype V] [Nonempty V]
    {p : V → Plane} {hp : Function.Injective p}
    (C : ∀ i : V, CentreProjectiveCycle hp i)
    (hcard : 3 ≤ Fintype.card V)
    {t : ℝ}
    (ht : 0 ≤ t) :
    (∃ r : V,
      (∑ i : V, 2 ^ centreExponent (C i) t) ≤
        deletionPostWeight
          (concreteDeletionAfter C hcard t) r)
    ∨
    (∃ i : V,
      (∀ j : V,
        centreExponent (C j) t ≤
          centreExponent (C i) t) ∧
      ConcreteDeletionUnitStable (C i) t) := by
  by_cases hcomp :
      ∃ r : V,
        (∑ i : V, 2 ^ centreExponent (C i) t) ≤
          deletionPostWeight
            (concreteDeletionAfter C hcard t) r
  · exact Or.inl hcomp
  · right
    have hnocomp :
        ∀ r : V,
          deletionPostWeight
              (concreteDeletionAfter C hcard t) r
            <
          ∑ i : V, 2 ^ centreExponent (C i) t := by
      intro r
      have hnot :
          ¬ (∑ i : V, 2 ^ centreExponent (C i) t) ≤
              deletionPostWeight
                (concreteDeletionAfter C hcard t) r := by
        intro hr
        exact hcomp ⟨r, hr⟩
      omega
    exact exists_concrete_maximal_stable_of_no_compensated
      C hcard ht hnocomp

/-- Inductive overweight form: if every deletion-completion is already under
B but the old configuration is over B, a maximal stable centre exists. -/
theorem exists_maximal_stable_of_overweight_and_children_bounded
    {V : Type*} [LinearOrder V] [Fintype V] [Nonempty V]
    {p : V → Plane} {hp : Function.Injective p}
    (C : ∀ i : V, CentreProjectiveCycle hp i)
    (hcard : 3 ≤ Fintype.card V)
    {t : ℝ}
    (ht : 0 ≤ t)
    (B : ℕ)
    (hover :
      B < ∑ i : V, 2 ^ centreExponent (C i) t)
    (hchild :
      ∀ r : V,
        deletionPostWeight
            (concreteDeletionAfter C hcard t) r ≤ B) :
    ∃ i : V,
      (∀ j : V,
        centreExponent (C j) t ≤
          centreExponent (C i) t) ∧
      ConcreteDeletionUnitStable (C i) t := by
  rcases concrete_compensated_or_maximal_stable
      C hcard ht with hcomp | hstable
  · obtain ⟨r, hr⟩ := hcomp
    have := hchild r
    omega
  · exact hstable

/-- Sharp Sendov dyadic specialization. -/
theorem exists_maximal_stable_of_overweight_two_pow
    {V : Type*} [LinearOrder V] [Fintype V] [Nonempty V]
    {p : V → Plane} {hp : Function.Injective p}
    (C : ∀ i : V, CentreProjectiveCycle hp i)
    (hcard : 3 ≤ Fintype.card V)
    {t : ℝ}
    (ht : 0 ≤ t)
    (n : ℕ)
    (hover :
      2 ^ n < ∑ i : V, 2 ^ centreExponent (C i) t)
    (hchild :
      ∀ r : V,
        deletionPostWeight
            (concreteDeletionAfter C hcard t) r ≤ 2 ^ n) :
    ∃ i : V,
      (∀ j : V,
        centreExponent (C j) t ≤
          centreExponent (C i) t) ∧
      ConcreteDeletionUnitStable (C i) t :=
  exists_maximal_stable_of_overweight_and_children_bounded
    C hcard ht (2 ^ n) hover hchild

/-- Final local induction outlet: to close one cardinality step it is enough
to prove the target directly whenever a maximal stable centre exists. -/
theorem concrete_capacity_of_children_and_stable_max
    {V : Type*} [LinearOrder V] [Fintype V] [Nonempty V]
    {p : V → Plane} {hp : Function.Injective p}
    (C : ∀ i : V, CentreProjectiveCycle hp i)
    (hcard : 3 ≤ Fintype.card V)
    {t : ℝ}
    (ht : 0 ≤ t)
    (B : ℕ)
    (hchild :
      ∀ r : V,
        deletionPostWeight
            (concreteDeletionAfter C hcard t) r ≤ B)
    (hstableCap :
      ∀ i : V,
        (∀ j : V,
          centreExponent (C j) t ≤
            centreExponent (C i) t) →
        ConcreteDeletionUnitStable (C i) t →
        (∑ j : V, 2 ^ centreExponent (C j) t) ≤ B) :
    (∑ j : V, 2 ^ centreExponent (C j) t) ≤ B := by
  by_contra hoverNot
  have hover :
      B < ∑ j : V, 2 ^ centreExponent (C j) t := by
    omega
  obtain ⟨i, hmax, hstable⟩ :=
    exists_maximal_stable_of_overweight_and_children_bounded
      C hcard ht B hover hchild
  exact (not_lt_of_ge (hstableCap i hmax hstable)) hover

#print axioms concrete_compensated_or_maximal_stable
#print axioms exists_maximal_stable_of_overweight_and_children_bounded
#print axioms concrete_capacity_of_children_and_stable_max

end JSP000404Research
