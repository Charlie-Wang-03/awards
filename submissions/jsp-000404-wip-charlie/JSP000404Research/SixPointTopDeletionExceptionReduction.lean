import JSP000404Research.SixPointSupportMultiplicityReduction
import JSP000404Research.SixPointConcreteTopDeletion
import Mathlib.Tactic

/-!
# Six-point top deletion: certified reduction to exceptional low-support centres

The genuine planar support-multiplicity theorem gives three cases for a
six-vertex configuration with one top exponent n-1 and five minima n-3.
If four minima have quotient support three, the *real deletion of the
top vertex* increases four survivor exponents and the child mass exceeds
2^n (indeed it is at least 9*2^(n-3)).

Consequently, IF this particular child is subject to a <=2^n
inductive bound, the four-support-three alternative is impossible,
and the only remaining motifs involve a support-one/support-two pair
or two distinct support-two centres.

The latter alternatives are NOT geometrically excluded here. This is
a necessary conditional reduction, NOT a proof of the JSP-000404 conjecture.
-/

namespace JSP000404Research

open scoped BigOperators

theorem six_point_top_deletion_overweight_or_low_support
    {V : Type*} [LinearOrder V] [Fintype V] [DecidableEq V]
    {p : V → Plane} (hp : Function.Injective p)
    {lam t delta : ℝ} {n : ℕ}
    (hcap : AngleCap p lam)
    (C : ∀ i : V, CentreProjectiveCycle hp i)
    (hn5 : 5 ≤ n)
    (hdelta0 : 0 ≤ delta)
    (hdeltaHalf : delta < (1 : ℝ) / 2)
    (ht : t = (n : ℝ) + delta)
    (hlam : lam = Real.pi / t)
    (hcard : Fintype.card V = 6)
    (top : V)
    (hTop : centreExponent (C top) t = n - 1)
    (hMin :
      ∀ v : V, v ≠ top →
        centreExponent (C v) t = n - 3) :
    (2 ^ n <
      ∑ v ∈ (Finset.univ.erase top : Finset V),
        2 ^ exponentAfterDeleteTopAt C
          (by omega : 3 ≤ Fintype.card V) top t v)
    ∨
    (∃ a b : V,
      a ≠ top ∧ b ≠ top ∧ a ≠ b ∧
      positiveSupport (centreQuotient (C a) t) = 1 ∧
      positiveSupport (centreQuotient (C b) t) = 2)
    ∨
    (∃ a b : V,
      a ≠ top ∧ b ≠ top ∧ a ≠ b ∧
      positiveSupport (centreQuotient (C a) t) = 2 ∧
      positiveSupport (centreQuotient (C b) t) = 2) := by
  classical
  have hcases :=
    six_point_support_multiplicity_reduction
      hp hcap C hn5 hdelta0 hdeltaHalf ht hlam
      hcard top hTop hMin
  rcases hcases with hfour | h12 | h22
  · have hfour' :
        4 ≤ ((Finset.univ.erase top : Finset V).filter
          (fun v =>
            positiveSupport (centreQuotient (C v) t) = 3)).card := hfour
    obtain ⟨good, hgoodFiltered, hgoodCard⟩ :=
      Finset.exists_subset_card_eq hfour'
    have hgoodSub :
        good ⊆ (Finset.univ.erase top : Finset V) :=
      hgoodFiltered.trans (Finset.filter_subset _ _)
    have hgoodSupport :
        ∀ v ∈ good,
          positiveSupport (centreQuotient (C v) t) = 3 := by
      intro v hv
      exact (Finset.mem_filter.mp (hgoodFiltered hv)).2
    have hweight :=
      six_point_top_deletion_compensated_of_four_support_three
        hp hcap C hn5 hdelta0 hdeltaHalf ht hlam
        hcard top hTop hMin good
        hgoodSub hgoodCard hgoodSupport
    have htopPow :
        (2 : ℕ) ^ (n - 1) = 4 * 2 ^ (n - 3) := by
      have hnEq : n - 1 = (n - 3) + 2 := by omega
      rw [hnEq, pow_add]
      norm_num
      ring
    have hnPow :
        (2 : ℕ) ^ n = 8 * 2 ^ (n - 3) := by
      have hnEq : n = (n - 3) + 3 := by omega
      rw [hnEq, pow_add]
      norm_num
      ring
    have hstrict :
        (2 : ℕ) ^ n <
          2 ^ (n - 1) + 5 * 2 ^ (n - 3) := by
      rw [htopPow, hnPow]
      have hpos : 0 < (2 : ℕ) ^ (n - 3) := by positivity
      omega
    exact Or.inl (lt_of_lt_of_le hstrict hweight)
  · exact Or.inr (Or.inl h12)
  · exact Or.inr (Or.inr h22)

/-- If the actual top-deleted five-centre child has the *separately
proved* capacity <=2^n, the only surviving top-centre six-point
motifs require at least two original low-support centres. -/
theorem six_point_bounded_top_child_forces_low_support
    {V : Type*} [LinearOrder V] [Fintype V] [DecidableEq V]
    {p : V → Plane} (hp : Function.Injective p)
    {lam t delta : ℝ} {n : ℕ}
    (hcap : AngleCap p lam)
    (C : ∀ i : V, CentreProjectiveCycle hp i)
    (hn5 : 5 ≤ n)
    (hdelta0 : 0 ≤ delta)
    (hdeltaHalf : delta < (1 : ℝ) / 2)
    (ht : t = (n : ℝ) + delta)
    (hlam : lam = Real.pi / t)
    (hcard : Fintype.card V = 6)
    (top : V)
    (hTop : centreExponent (C top) t = n - 1)
    (hMin :
      ∀ v : V, v ≠ top →
        centreExponent (C v) t = n - 3)
    (hchild :
      (∑ v ∈ (Finset.univ.erase top : Finset V),
        2 ^ exponentAfterDeleteTopAt C
          (by omega : 3 ≤ Fintype.card V) top t v) ≤ 2 ^ n) :
    (∃ a b : V,
      a ≠ top ∧ b ≠ top ∧ a ≠ b ∧
      positiveSupport (centreQuotient (C a) t) = 1 ∧
      positiveSupport (centreQuotient (C b) t) = 2)
    ∨
    (∃ a b : V,
      a ≠ top ∧ b ≠ top ∧ a ≠ b ∧
      positiveSupport (centreQuotient (C a) t) = 2 ∧
      positiveSupport (centreQuotient (C b) t) = 2) := by
  have h := six_point_top_deletion_overweight_or_low_support
    hp hcap C hn5 hdelta0 hdeltaHalf ht hlam
    hcard top hTop hMin
  rcases h with hover | hlow
  · exact False.elim ((Nat.not_lt_of_ge hchild) hover)
  · exact hlow

#print axioms six_point_top_deletion_overweight_or_low_support
#print axioms six_point_bounded_top_child_forces_low_support

end JSP000404Research
