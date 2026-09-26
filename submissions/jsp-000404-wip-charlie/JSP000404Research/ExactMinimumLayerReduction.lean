
import JSP000404Research.ExactMinimumDeletionCandidate
import Mathlib.Tactic

/-!
# Exact minimum-layer reduction relative to one maximum-angle witness

Fix an exact angle witness W=(a,b,c) for the current normalization.

Let M be the minimum-exponent layer.

There is a sharper dichotomy than the cardinality-based selection used in
ExactMinimumDeletionCandidate:

* either every minimum vertex lies in the witness triple {a,b,c};
* or there is a minimum vertex r outside the witness triple.

In the second case deleting r preserves the exact normalization.  If the
induction hypothesis bounds every witness-avoiding child by 2^n, the
one-column minimal-overweight rigidity theorem immediately forces the r
deletion column to be exact and pointwise rigid.

Thus every minimal overweight exact counterexample reduces to a terminal
configuration whose entire minimum layer is contained in one fixed
maximum-angle witness triple, unless an exact rigid minimum deletion is
available.
-/

namespace JSP000404Research

open scoped BigOperators

noncomputable def exactWitnessTriple
    {V : Type*}
    {p : V → Plane} {lam : ℝ}
    (W : ExactAngleWitness p lam) : Finset V := by
  classical
  exact {W.a, W.b, W.c}

@[simp] theorem mem_exactWitnessTriple
    {V : Type*}
    {p : V → Plane} {lam : ℝ}
    (W : ExactAngleWitness p lam)
    (v : V) :
    v ∈ exactWitnessTriple W ↔
      v = W.a ∨ v = W.b ∨ v = W.c := by
  classical
  simp [exactWitnessTriple]

theorem exactWitnessTriple_card_eq_three
    {V : Type*}
    {p : V → Plane} {lam : ℝ}
    (W : ExactAngleWitness p lam) :
    (exactWitnessTriple W).card = 3 := by
  classical
  simp [exactWitnessTriple, W.hab, W.hac, W.hbc]

/-- A minimum vertex outside the witness triple exists exactly when the
minimum layer is not contained in the witness triple. -/
theorem exists_minimum_outside_witness_of_not_subset
    {V : Type*} [Fintype V] [DecidableEq V]
    {p : V → Plane} {lam : ℝ}
    (exponent : V → ℕ)
    (r0 : V)
    (W : ExactAngleWitness p lam)
    (hnot :
      ¬ minimumExponentVertices exponent r0 ⊆
        exactWitnessTriple W) :
    ∃ r : V,
      exponent r = exponent r0 ∧
      r ≠ W.a ∧ r ≠ W.b ∧ r ≠ W.c := by
  classical
  obtain ⟨r, hrM, hrT⟩ :=
    Finset.not_subset.mp hnot
  have hrMin :
      exponent r = exponent r0 :=
    (mem_minimumExponentVertices exponent r0 r).1 hrM
  have hrAvoid :
      r ≠ W.a ∧ r ≠ W.b ∧ r ≠ W.c := by
    simpa [exactWitnessTriple] using hrT
  exact ⟨r, hrMin,
    hrAvoid.1, hrAvoid.2.1, hrAvoid.2.2⟩

/-- Main exact minimum-layer dichotomy. -/
theorem minimum_layer_subset_witness_or_exact_rigid_deletion
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
    minimumExponentVertices
        (fun i => centreExponent (C i) t) r0
      ⊆ exactWitnessTriple W
    ∨
    ∃ r : V,
      centreExponent (C r) t =
          centreExponent (C r0) t
      ∧ r ≠ W.a ∧ r ≠ W.b ∧ r ≠ W.c
      ∧ ExactAngleCap (deletePoint p r) lam
      ∧
      ((∑ i : V, 2 ^ centreExponent (C i) t) - 2 ^ n =
          2 ^ centreExponent (C r) t)
      ∧ deletionPostWeight
          (concreteDeletionAfter C hV t) r = 2 ^ n
      ∧ ∀ i : V, i ≠ r →
          concreteDeletionAfter C hV t r i =
            centreExponent (C i) t := by
  classical
  let M :=
    minimumExponentVertices
      (fun i => centreExponent (C i) t) r0
  by_cases hsub :
      M ⊆ exactWitnessTriple W
  · exact Or.inl hsub
  · right
    obtain ⟨r, hrMin, hra, hrb, hrc⟩ :=
      exists_minimum_outside_witness_of_not_subset
        (fun i => centreExponent (C i) t)
        r0 W (by simpa [M] using hsub)
    have hminR :
        ∀ i : V,
          centreExponent (C r) t ≤
            centreExponent (C i) t := by
      intro i
      rw [hrMin]
      exact hmin i
    have hrig :=
      concrete_minimum_deletion_rigidity_of_child_bound
        C hV ht0 n r hexp hover
        (hchild r hra hrb hrc) hminR
    have hexact :
        ExactAngleCap (deletePoint p r) lam :=
      exactAngleCap_deletePoint_of_avoids_witness
        hcap W r hra hrb hrc
    exact ⟨r, hrMin, hra, hrb, hrc, hexact,
      hrig.1, hrig.2.1, hrig.2.2⟩

/-- Terminal branch cardinality: if all minimum vertices lie in the fixed
exact witness triple, there are at most three of them. -/
theorem minimum_layer_card_le_three_of_subset_witness
    {V : Type*} [Fintype V] [DecidableEq V]
    {p : V → Plane} {lam : ℝ}
    (exponent : V → ℕ)
    (r0 : V)
    (W : ExactAngleWitness p lam)
    (hsub :
      minimumExponentVertices exponent r0 ⊆
        exactWitnessTriple W) :
    (minimumExponentVertices exponent r0).card ≤ 3 := by
  have hle := Finset.card_le_card hsub
  rw [exactWitnessTriple_card_eq_three W] at hle
  exact hle

/-- If the terminal minimum layer has all three vertices, it is exactly the
witness triple. -/
theorem minimum_layer_eq_witness_of_card_three
    {V : Type*} [Fintype V] [DecidableEq V]
    {p : V → Plane} {lam : ℝ}
    (exponent : V → ℕ)
    (r0 : V)
    (W : ExactAngleWitness p lam)
    (hsub :
      minimumExponentVertices exponent r0 ⊆
        exactWitnessTriple W)
    (hcard :
      (minimumExponentVertices exponent r0).card = 3) :
    minimumExponentVertices exponent r0 =
      exactWitnessTriple W := by
  apply Finset.eq_of_subset_of_card_le hsub
  rw [hcard, exactWitnessTriple_card_eq_three W]

#print axioms exists_minimum_outside_witness_of_not_subset
#print axioms minimum_layer_subset_witness_or_exact_rigid_deletion
#print axioms minimum_layer_card_le_three_of_subset_witness
#print axioms minimum_layer_eq_witness_of_card_three

end JSP000404Research
