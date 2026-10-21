import JSP000404Research.ThreeFiveNoTopWeight
import JSP000404Research.PlanarUniqueTopExponent
import JSP000404Research.FiveCentreNoSecondLayerCapacity
import Mathlib.Tactic

/-!
# Genuine planar n=3 / five-centre overweight profile dichotomy

All assumptions refer to the ACTUAL planar AngleCap and
CentreProjectiveCycle exponent data, not auxiliary abstract payment credits.
Any capacity violation at n=3 on five centres must lie in one of two
still-geometrically-unresolved motifs:
* No top exponent 2, and at least four exponent-1 centres.
* Exactly one exponent-2 centre and exactly one exponent-1 centre.

The theorem classifies possible failures; it does not disprove their
geometric realization and does not discharge the global six-source theorem.
-/

namespace JSP000404Research

open scoped BigOperators

theorem planar_three_five_overweight_profile_dichotomy
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
    (hover :
      8 < (∑ i : V, (2 : ℕ) ^ centreExponent (C i) t)) :
    ((∀ i : V, centreExponent (C i) t ≤ 1) ∧
      4 ≤ ((Finset.univ : Finset V).filter
        (fun i => centreExponent (C i) t = 1)).card) ∨
    (∃ s a : V, s ≠ a ∧
      centreExponent (C s) t = 2 ∧
      centreExponent (C a) t = 1 ∧
      (∀ b : V, b ≠ s →
        centreExponent (C b) t = 1 → b = a)) := by
  classical
  let k : V → ℕ := fun i => centreExponent (C i) t
  have hdelta1 : delta < 1 := by linarith
  have hk : ∀ i : V, k i ≤ 2 := by
    intro i
    have hi := centreExponent_lt_n
      (C i) 3 delta t
      (by omega : 1 ≤ (3 : ℕ)) hdelta0 hdelta1 ht
    dsimp [k]
    omega
  have hcard3 : 3 ≤ Fintype.card V := by omega
  have hcard4 : 4 ≤ Fintype.card V := by omega
  by_cases htop : ∃ s : V, k s = 2
  · right
    obtain ⟨s, hs⟩ := htop
    have hunique : ∀ i : V, i ≠ s → k i ≠ 2 := by
      intro i his hi
      exact top_exponent_unique_of_card_ge_three
        hp hcap (by omega : 3 ≤ (3 : ℕ)) hcard3
        hdelta0 hdeltaHalf ht hlam C s i his.symm
        (by simpa [k] using hs)
        (by simpa [k] using hi)
    have hnext : ∃ a : V, k a = 1 := by
      by_contra hnone
      have hother : ∀ i : V, i ≠ s → k i ≤ 0 := by
        intro i his
        have hi := hk i
        have hinot2 := hunique i his
        have hinot1 : k i ≠ 1 := by
          intro h
          exact hnone ⟨i, h⟩
        omega
      have hcapacity : (∑ i : V, (2 : ℕ) ^ k i) ≤ 8 := by
        have h := dyadic_capacity_of_top_and_four_low
          k 3 s (by omega : 3 ≤ (3 : ℕ))
          (by omega : Fintype.card V ≤ 5)
          (by simpa using hs)
          (by
            intro i his
            simpa using hother i his)
        simpa using h
      have hover' : 8 < (∑ i : V, (2 : ℕ) ^ k i) := by
        simpa [k] using hover
      omega
    obtain ⟨a, ha⟩ := hnext
    have hsa : s ≠ a := by
      intro heq
      rw [heq] at hs
      omega
    refine ⟨s, a, hsa, ?_, ?_, ?_⟩
    · simpa [k] using hs
    · simpa [k] using ha
    · intro b hbs hb
      by_contra hba
      exact no_two_next_exponents_beside_top_of_card_ge_four
        hp hcap (by omega : 3 ≤ (3 : ℕ)) hcard4
        hdelta0 hdeltaHalf ht hlam C
        hsa hbs hba
        (by simpa [k] using hs)
        (by simpa [k] using ha)
        (by simpa [k] using hb)
  · left
    have hnoTop : ∀ i : V, k i ≤ 1 := by
      intro i
      have hi := hk i
      have hinot2 : k i ≠ 2 := by
        intro h
        exact htop ⟨i, h⟩
      omega
    constructor
    · exact hnoTop
    · exact five_centre_no_top_overweight_forces_four_next
        k hcard hnoTop (by simpa [k] using hover)

#print axioms planar_three_five_overweight_profile_dichotomy

end JSP000404Research
