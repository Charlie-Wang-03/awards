import JSP000404Research.ThreeFiveOverweightPlanarMotifs
import Mathlib.Tactic

/-!
# Exact n=3 five-centre dyadic mass and forbidden-profile equivalence

This file is a kernel-checked classification of the remaining FIVE actual
planar-centre profiles. It does not exclude either forbidden profile.
It replaces the one-way overweight implication with an exact equivalence.
In particular it does not assume a six-source payment, and it cannot
close the general arbitrary-cardinality problem on its own.
-/

namespace JSP000404Research

open scoped BigOperators

/-- Every exponent in {0,1,2} contributes its baseline unit,
one extra unit if it equals one, and three extra units if it equals two. -/
theorem ternary_dyadic_sum_exact
    {V : Type*} [Fintype V]
    (k : V → ℕ)
    (hk : ∀ i : V, k i ≤ 2) :
    (∑ i : V, (2 : ℕ) ^ k i) =
      Fintype.card V +
        ((Finset.univ : Finset V).filter (fun i => k i = 1)).card +
        3 * ((Finset.univ : Finset V).filter (fun i => k i = 2)).card := by
  classical
  have hpoint (i : V) :
      (2 : ℕ) ^ k i =
        1 + (if k i = 1 then 1 else 0) +
          3 * (if k i = 2 then 1 else 0) := by
    have hi := hk i
    interval_cases h : k i <;> simp [h] at *
  calc
    (∑ i : V, (2 : ℕ) ^ k i) =
        ∑ i : V, (1 + (if k i = 1 then 1 else 0) +
          3 * (if k i = 2 then 1 else 0)) := by
            apply Finset.sum_congr rfl
            intro i _
            exact hpoint i
    _ = Fintype.card V +
          ((Finset.univ : Finset V).filter (fun i => k i = 1)).card +
          3 * ((Finset.univ : Finset V).filter (fun i => k i = 2)).card := by
            simp [Finset.sum_add_distrib, Finset.mul_sum]

/-- The actual planar n=3 five-centre mass has an exact finite census.
No extra geometric assumptions beyond AngleCap are introduced. -/
theorem planar_three_five_dyadic_mass_exact
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane}
    (hp : Function.Injective p)
    {lam t delta : ℝ}
    (hcap : AngleCap p lam)
    (hcard : Fintype.card V = 5)
    (hdelta0 : 0 ≤ delta)
    (hdeltaHalf : delta < (1 : ℝ) / 2)
    (ht : t = (3 : ℝ) + delta)
    (hlam : lam = Real.pi / t)
    (C : ∀ i : V, CentreProjectiveCycle hp i) :
    (∑ i : V, (2 : ℕ) ^ centreExponent (C i) t) =
      5 +
        ((Finset.univ : Finset V).filter
          (fun i => centreExponent (C i) t = 1)).card +
        3 * ((Finset.univ : Finset V).filter
          (fun i => centreExponent (C i) t = 2)).card := by
  have hdelta1 : delta < 1 := by linarith
  have hk : ∀ i : V, centreExponent (C i) t ≤ 2 := by
    intro i
    have hi := centreExponent_lt_n (C i) 3 delta t
      (by omega : 1 ≤ (3 : ℕ)) hdelta0 hdelta1 ht
    omega
  simpa [hcard] using
    (ternary_dyadic_sum_exact (fun i => centreExponent (C i) t) hk)

/-- Exact equivalence: a five-centre n=3 planar mass violation occurs
if and only if one of the two concrete exceptional geometric profiles
is realized. The two profiles themselves remain to be eliminated. -/
theorem planar_three_five_overweight_iff_two_motifs
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane}
    (hp : Function.Injective p)
    {lam t delta : ℝ}
    (hcap : AngleCap p lam)
    (hcard : Fintype.card V = 5)
    (hdelta0 : 0 ≤ delta)
    (hdeltaHalf : delta < (1 : ℝ) / 2)
    (ht : t = (3 : ℝ) + delta)
    (hlam : lam = Real.pi / t)
    (C : ∀ i : V, CentreProjectiveCycle hp i) :
    (8 < (∑ i : V, (2 : ℕ) ^ centreExponent (C i) t)) ↔
      ((∀ i : V, centreExponent (C i) t ≤ 1) ∧
        4 ≤ ((Finset.univ : Finset V).filter
          (fun i => centreExponent (C i) t = 1)).card) ∨
      (∃ s a : V, s ≠ a ∧
        centreExponent (C s) t = 2 ∧
        centreExponent (C a) t = 1 ∧
        (∀ b : V, b ≠ s →
          centreExponent (C b) t = 1 → b = a)) := by
  constructor
  · exact planar_three_five_overweight_profile_dichotomy
      hp hcap hcard hdelta0 hdeltaHalf ht hlam C
  · intro h
    rcases h with ⟨hk, hfour⟩ | ⟨s, a, hsa, hs, ha, _hunique⟩
    · have heq :=
        zero_one_dyadic_sum_eq_card_add_ones
          (fun i => centreExponent (C i) t) hk
      rw [heq, hcard]
      omega
    · have hsum := planar_three_five_dyadic_mass_exact
        hp hcap hcard hdelta0 hdeltaHalf ht hlam C
      have hone :
          0 < ((Finset.univ : Finset V).filter
            (fun i => centreExponent (C i) t = 1)).card := by
        apply Finset.card_pos.mpr
        exact ⟨a, by simp [ha]⟩
      have htop :
          0 < ((Finset.univ : Finset V).filter
            (fun i => centreExponent (C i) t = 2)).card := by
        apply Finset.card_pos.mpr
        exact ⟨s, by simp [hs]⟩
      rw [hsum]
      omega

#print axioms ternary_dyadic_sum_exact
#print axioms planar_three_five_dyadic_mass_exact
#print axioms planar_three_five_overweight_iff_two_motifs

end JSP000404Research
