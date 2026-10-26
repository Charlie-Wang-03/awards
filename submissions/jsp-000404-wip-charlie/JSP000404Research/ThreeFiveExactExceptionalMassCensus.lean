import JSP000404Research.ThreeFiveExactOverweightEquivalence
import Mathlib.Tactic

/-!
# Exact possible overweight masses for five real centres in the n = 3 strip

The previous exact planar geometric dichotomy showed that any REAL
AngleCap five-centre n=3 overweight profile has exactly one of two
types: (A) no exponent-two and >=4 exponent-one centres, or
(B) one exponent-two centre and exactly one exponent-one centre.

We now recover its FULL INTEGER mass, with no abstract debt-token
assumption and no auxiliary Hall expansion:
  * type A has dyadic total exactly 9 or 10;
  * type B has dyadic total exactly 9.

This eliminates ALL larger numerical counterexample profiles in this
original five-centre strip, leaving only the geometric exclusion of
the two exceptional motifs. It does NOT claim either motif impossible.
-/

namespace JSP000404Research
open scoped BigOperators

/-- The genuine n=3, five-original-centre AngleCap configuration
cannot have dyadic mass >10; every overweight counterexample has
the *EXACT* total 9 or 10. A stronger finite numerical profile
reduction than just the original one-way overweight motif dichotomy. -/
theorem planar_three_five_overweight_mass_eq_nine_or_ten
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
    (C : ∀ i : V, CentreProjectiveCycle hp i)
    (hover : 8 < (∑ i : V, (2 : ℕ) ^ centreExponent (C i) t)) :
    (∑ i : V, (2 : ℕ) ^ centreExponent (C i) t) = 9 ∨
      (∑ i : V, (2 : ℕ) ^ centreExponent (C i) t) = 10 := by
  classical
  have hmass :=
    planar_three_five_dyadic_mass_exact
      hp hcap hcard hdelta0 hdeltaHalf ht hlam C
  have hcases :=
    (planar_three_five_overweight_iff_two_motifs
      hp hcap hcard hdelta0 hdeltaHalf ht hlam C).mp hover
  rcases hcases with ⟨hnTop, hfour⟩ | ⟨s,a,hsa,hs,ha,hnextUnique⟩
  · have hnoTwo :
        ((Finset.univ : Finset V).filter
          (fun i => centreExponent (C i) t = 2)) = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro i hi
      have hii := (Finset.mem_filter.mp hi).2
      have hle := hnTop i
      omega
    have hcount :
        ((Finset.univ : Finset V).filter
          (fun i => centreExponent (C i) t = 1)).card ≤ 5 := by
      have h := Finset.card_le_univ
        ((Finset.univ : Finset V).filter
          (fun i => centreExponent (C i) t = 1))
      omega
    rw [hnoTwo] at hmass
    simp only [Finset.card_empty, mul_zero, add_zero] at hmass
    omega
  · have htopUnique : ∀ i : V,
        centreExponent (C i) t = 2 → i = s := by
      intro i hi
      by_contra hne
      exact top_exponent_unique_of_card_ge_three
        hp hcap (by decide : 3 ≤ (3 : ℕ))
        (by omega : 3 ≤ Fintype.card V)
        hdelta0 hdeltaHalf ht hlam C s i hne.symm hs hi
    have hOne :
        ((Finset.univ : Finset V).filter
          (fun i => centreExponent (C i) t = 1)) = {a} := by
      ext i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and,
        Finset.mem_singleton]
      constructor
      · intro hi
        by_cases his : i = s
        · rw [his, hs] at hi
          omega
        · exact hnextUnique i his hi
      · intro hi
        rw [hi]
        exact ha
    have hTwo :
        ((Finset.univ : Finset V).filter
          (fun i => centreExponent (C i) t = 2)) = {s} := by
      ext i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and,
        Finset.mem_singleton]
      constructor
      · exact htopUnique i
      · intro hi
        rw [hi]
        exact hs
    left
    simpa [hOne, hTwo] using hmass

#print axioms planar_three_five_overweight_mass_eq_nine_or_ten

end JSP000404Research
