import JSP000404Research.ThreeFiveExactExceptionalMassCensus
import Mathlib.Tactic

/-!
# n=3: maximum five-centre overweight MASS=10 iff EVERY exponent is ONE

The real planar five-centre \`AngleCap\` exclusion of two top-exponent
vertices and of two next vertices next to a top leaves two overweight
profile classes. The exact dyadic census now shows that the MAXIMAL
remaining numerical exception, weight 10, has *exactly one* possible
profile: every one of the FIVE original centres has exponent 1.

This is an unconditional structural reduction under ORIGINAL planar
geometry, not a claim that this exceptional profile exists, nor a
completion of the global all-cardinality proof.
-/

namespace JSP000404Research
open scoped BigOperators

theorem planar_three_five_mass_ten_iff_all_next
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
    (∑ i : V, (2 : ℕ) ^ centreExponent (C i) t) = 10 ↔
      ∀ i : V, centreExponent (C i) t = 1 := by
  classical
  constructor
  · intro hten
    have hover : 8 < (∑ i : V, (2 : ℕ) ^ centreExponent (C i) t) := by
      omega
    have hmotif :=
      (planar_three_five_overweight_iff_two_motifs
        hp hcap hcard hdelta0 hdeltaHalf ht hlam C).mp hover
    have hmass := planar_three_five_dyadic_mass_exact
      hp hcap hcard hdelta0 hdeltaHalf ht hlam C
    rcases hmotif with ⟨hnoTop, _hfour⟩ | ⟨s,a,hsa,hs,ha,hnextUnique⟩
    · have hnoTwo :
          ((Finset.univ : Finset V).filter
            (fun i => centreExponent (C i) t = 2)) = ∅ := by
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro i hi
        have hii := (Finset.mem_filter.mp hi).2
        have hle := hnoTop i
        omega
      rw [hnoTwo] at hmass
      simp only [Finset.card_empty, mul_zero, add_zero] at hmass
      have hfive :
          ((Finset.univ : Finset V).filter
            (fun i => centreExponent (C i) t = 1)).card = 5 := by
        omega
      have hsubset :
          ((Finset.univ : Finset V).filter
            (fun i => centreExponent (C i) t = 1)) ⊆
          (Finset.univ : Finset V) := Finset.filter_subset _ _
      have huniv :
          ((Finset.univ : Finset V).filter
            (fun i => centreExponent (C i) t = 1)) =
          (Finset.univ : Finset V) := by
        apply Finset.eq_of_subset_of_card_le hsubset
        simpa [hcard] using hfive.ge
      intro i
      have hi :
          i ∈ (Finset.univ : Finset V).filter
            (fun i => centreExponent (C i) t = 1) := by
        rw [huniv]
        exact Finset.mem_univ i
      exact (Finset.mem_filter.mp hi).2
    · have htopUnique : ∀ i : V,
          centreExponent (C i) t = 2 → i = s := by
        intro i hi
        by_contra hne
        have hsi : s ≠ i := by
          intro hsi
          exact hne hsi.symm
        exact top_exponent_unique_of_card_ge_three
          hp hcap (by decide : 3 ≤ (3 : ℕ))
          (by omega : 3 ≤ Fintype.card V)
          hdelta0 hdeltaHalf ht hlam C s i hsi hs hi
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
      simp only [hOne, hTwo, Finset.card_singleton] at hmass
      omega
  · intro hall
    calc
      (∑ i : V, (2 : ℕ) ^ centreExponent (C i) t) =
          ∑ _i : V, (2 : ℕ) := by
            apply Finset.sum_congr rfl
            intro i _
            simp [hall i]
      _ = 10 := by simp [hcard]

#print axioms planar_three_five_mass_ten_iff_all_next

end JSP000404Research
