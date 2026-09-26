
import JSP000404Research.ExactAngleWitnessRestriction
import JSP000404Research.ConcreteMinimumOverweightRigidity
import JSP000404Research.MinimalOverweightParity
import Mathlib.Tactic

/-!
# A minimum-exponent exact-normalization deletion outside the witness triple

Fix one exact maximum-angle witness W=(a,b,c).  If the minimum-exponent layer
has more than three vertices, at least one minimum vertex lies outside this
triple.

Deleting such a vertex preserves the same exact angle normalization lambda.
Hence an induction hypothesis stated for exact-normalized children may be
applied at the unchanged t=pi/lambda.

Once that one child is known to satisfy the sharp 2^n capacity, the
one-column minimal-overweight rigidity theorem forces:

* old overweight excess = the deleted minimum dyadic weight;
* post-deletion mass = 2^n;
* every survivor exponent is unchanged.

This file packages the exact-normalization selection and the one-column
rigidity in one interface.
-/

namespace JSP000404Research

open scoped BigOperators

/-- If the minimum layer has more than three vertices, one minimum vertex
avoids any prescribed triple. -/
theorem exists_minimum_outside_triple_of_three_lt_card
    {V : Type*} [Fintype V] [DecidableEq V]
    (exponent : V → ℕ)
    (r0 a b c : V)
    (hmin :
      ∀ i : V, exponent r0 ≤ exponent i)
    (hcard :
      3 < (minimumExponentVertices exponent r0).card) :
    ∃ r : V,
      exponent r = exponent r0 ∧
      r ≠ a ∧ r ≠ b ∧ r ≠ c := by
  classical
  by_contra hnone
  push_neg at hnone
  have hsub :
      minimumExponentVertices exponent r0 ⊆ {a,b,c} := by
    intro r hr
    have hrmin :
        exponent r = exponent r0 :=
      (mem_minimumExponentVertices exponent r0 r).1 hr
    have hcases := hnone r hrmin
    simp only [Finset.mem_insert, Finset.mem_singleton]
    exact hcases
  have hle :=
    Finset.card_le_card hsub
  have htriple : ({a,b,c} : Finset V).card ≤ 3 := by
    simp
    omega
  omega

/-- Exact-witness specialization of the preceding selection theorem. -/
theorem exists_minimum_avoiding_exactWitness
    {V : Type*} [Fintype V] [DecidableEq V]
    {p : V → Plane} {lam : ℝ}
    (exponent : V → ℕ)
    (r0 : V)
    (hmin :
      ∀ i : V, exponent r0 ≤ exponent i)
    (W : ExactAngleWitness p lam)
    (hcard :
      3 < (minimumExponentVertices exponent r0).card) :
    ∃ r : V,
      exponent r = exponent r0 ∧
      r ≠ W.a ∧ r ≠ W.b ∧ r ≠ W.c := by
  exact exists_minimum_outside_triple_of_three_lt_card
    exponent r0 W.a W.b W.c hmin hcard

/-- Main exact-normalization one-column rigidity package.

If the minimum layer has more than three vertices, choose a minimum centre
outside the fixed exact witness triple.  Its deletion preserves the exact
angle normalization.  If that child is bounded by the induction hypothesis,
then the deletion column is completely rigid.
-/
theorem exists_exact_minimum_deletion_rigidity
    {V : Type*} [LinearOrder V] [Fintype V] [Nonempty V]
    {p : V → Plane} {hp : Function.Injective p}
    {lam t : ℝ}
    (hcap : AngleCap p lam)
    (W : ExactAngleWitness p lam)
    (C : ∀ i : V, CentreProjectiveCycle hp i)
    (hV : 3 ≤ Fintype.card V)
    (ht0 : 0 ≤ t)
    (n : ℕ)
    (r0 : V)
    (hexp :
      ∀ i : V, centreExponent (C i) t ≤ n)
    (hover :
      2 ^ n < ∑ i : V, 2 ^ centreExponent (C i) t)
    (hmin :
      ∀ i : V,
        centreExponent (C r0) t ≤
          centreExponent (C i) t)
    (hminCard :
      3 <
        (minimumExponentVertices
          (fun i => centreExponent (C i) t) r0).card)
    (hchild :
      ∀ r : V,
        r ≠ W.a → r ≠ W.b → r ≠ W.c →
        deletionPostWeight
            (concreteDeletionAfter C hV t) r
          ≤ 2 ^ n) :
    ∃ r : V,
      centreExponent (C r) t =
          centreExponent (C r0) t
      ∧ r ≠ W.a ∧ r ≠ W.b ∧ r ≠ W.c
      ∧ ExactAngleCap (deletePoint p r) lam
      ∧ deletionPostWeight
          (concreteDeletionAfter C hV t) r = 2 ^ n
      ∧ ∀ i : V, i ≠ r →
          concreteDeletionAfter C hV t r i =
            centreExponent (C i) t := by
  classical
  obtain ⟨r, hrmin, hra, hrb, hrc⟩ :=
    exists_minimum_avoiding_exactWitness
      (fun i => centreExponent (C i) t)
      r0 hmin W hminCard
  have hminR :
      ∀ i : V,
        centreExponent (C r) t ≤
          centreExponent (C i) t := by
    intro i
    rw [hrmin]
    exact hmin i
  have hchildR :
      deletionPostWeight
          (concreteDeletionAfter C hV t) r
        ≤ 2 ^ n :=
    hchild r hra hrb hrc
  have hrig :=
    concrete_minimum_deletion_rigidity_of_child_bound
      C hV ht0 n r hexp hover hchildR hminR
  have hexact :
      ExactAngleCap (deletePoint p r) lam :=
    exactAngleCap_deletePoint_of_avoids_witness
      hcap W r hra hrb hrc
  exact ⟨r, hrmin, hra, hrb, hrc, hexact,
    hrig.2.1, hrig.2.2⟩

/-- Dichotomy form convenient for induction: either the minimum layer has at
most three vertices, or there is an exact-normalization-preserving rigid
minimum deletion. -/
theorem minimum_layer_le_three_or_exact_rigid_deletion
    {V : Type*} [LinearOrder V] [Fintype V] [Nonempty V]
    {p : V → Plane} {hp : Function.Injective p}
    {lam t : ℝ}
    (hcap : AngleCap p lam)
    (W : ExactAngleWitness p lam)
    (C : ∀ i : V, CentreProjectiveCycle hp i)
    (hV : 3 ≤ Fintype.card V)
    (ht0 : 0 ≤ t)
    (n : ℕ)
    (r0 : V)
    (hexp :
      ∀ i : V, centreExponent (C i) t ≤ n)
    (hover :
      2 ^ n < ∑ i : V, 2 ^ centreExponent (C i) t)
    (hmin :
      ∀ i : V,
        centreExponent (C r0) t ≤
          centreExponent (C i) t)
    (hchild :
      ∀ r : V,
        r ≠ W.a → r ≠ W.b → r ≠ W.c →
        deletionPostWeight
            (concreteDeletionAfter C hV t) r
          ≤ 2 ^ n) :
    (minimumExponentVertices
      (fun i => centreExponent (C i) t) r0).card ≤ 3
    ∨
    ∃ r : V,
      centreExponent (C r) t =
          centreExponent (C r0) t
      ∧ r ≠ W.a ∧ r ≠ W.b ∧ r ≠ W.c
      ∧ ExactAngleCap (deletePoint p r) lam
      ∧ deletionPostWeight
          (concreteDeletionAfter C hV t) r = 2 ^ n
      ∧ ∀ i : V, i ≠ r →
          concreteDeletionAfter C hV t r i =
            centreExponent (C i) t := by
  classical
  by_cases hsmall :
      (minimumExponentVertices
        (fun i => centreExponent (C i) t) r0).card ≤ 3
  · exact Or.inl hsmall
  · right
    apply exists_exact_minimum_deletion_rigidity
      hcap W C hV ht0 n r0 hexp hover hmin
  · omega
  · exact hchild

#print axioms exists_minimum_outside_triple_of_three_lt_card
#print axioms exists_minimum_avoiding_exactWitness
#print axioms exists_exact_minimum_deletion_rigidity
#print axioms minimum_layer_le_three_or_exact_rigid_deletion

end JSP000404Research
