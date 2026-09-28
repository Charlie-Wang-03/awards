import JSP000404Research.ThirdLayerSupportOneMultiplicity
import JSP000404Research.ConcreteDeficitThree
import Mathlib.Tactic

/-!
# Global support-multiplicity reduction in the six-point third layer

The five non-top centres all have exponent n-3, so each quotient support is
exactly 1, 2, or 3.

The preceding packing theorem shows that at most one minimum can have support
one.  Therefore exactly one of the following coarse regimes occurs:

1. at least four minima have support three;
2. there is a support-one minimum and a distinct support-two minimum;
3. there are two distinct support-two minima.

The first regime is the compensated-top-deletion branch.  Thus all genuinely
hard six-point geometry is reduced to the mixed (1,2) and pure (2,2)
low-support regimes.
-/

namespace JSP000404Research

theorem six_point_support_multiplicity_reduction
    {V : Type*} [LinearOrder V] [Fintype V] [DecidableEq V]
    {p : V → Plane}
    (hp : Function.Injective p)
    (hcap : AngleCap p lam)
    (C : ∀ i : V, CentreProjectiveCycle hp i)
    {lam t delta : ℝ} {n : ℕ}
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
    let minima : Finset V := Finset.univ.erase top
    let support3 : Finset V :=
      minima.filter
        (fun v =>
          positiveSupport (centreQuotient (C v) t) = 3)
    (4 ≤ support3.card)
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
  dsimp only
  let minima : Finset V := Finset.univ.erase top
  let support3 : Finset V :=
    minima.filter
      (fun v =>
        positiveSupport (centreQuotient (C v) t) = 3)

  have hminCard : minima.card = 5 := by
    dsimp [minima]
    rw [Finset.card_erase_of_mem (Finset.mem_univ top),
        Finset.card_univ, hcard]

  by_cases hfour : 4 ≤ support3.card
  · exact Or.inl hfour

  have hs3le : support3.card ≤ 3 := by omega
  let low : Finset V := minima \ support3
  have hlowCard : 2 ≤ low.card := by
    have hsub : support3 ⊆ minima := by
      intro v hv
      exact (Finset.mem_filter.mp hv).1
    have hcardLow :
        low.card = minima.card - support3.card := by
      dsimp [low]
      rw [Finset.card_sdiff hsub]
    rw [hcardLow, hminCard]
    omega

  obtain ⟨a,ha,b,hb,hab⟩ :=
    Finset.two_le_card.mp hlowCard

  have haMin : a ∈ minima := (Finset.mem_sdiff.mp ha).1
  have hbMin : b ∈ minima := (Finset.mem_sdiff.mp hb).1
  have hat : a ≠ top := by
    simpa [minima] using (Finset.mem_erase.mp haMin).1
  have hbt : b ≠ top := by
    simpa [minima] using (Finset.mem_erase.mp hbMin).1

  have haNot3 :
      positiveSupport (centreQuotient (C a) t) ≠ 3 := by
    intro h3
    have : a ∈ support3 := by
      exact Finset.mem_filter.mpr ⟨haMin,h3⟩
    exact (Finset.mem_sdiff.mp ha).2 this
  have hbNot3 :
      positiveSupport (centreQuotient (C b) t) ≠ 3 := by
    intro h3
    have : b ∈ support3 := by
      exact Finset.mem_filter.mpr ⟨hbMin,h3⟩
    exact (Finset.mem_sdiff.mp hb).2 this

  have support12 :
      ∀ v : V, v ≠ top →
        positiveSupport (centreQuotient (C v) t) = 1 ∨
        positiveSupport (centreQuotient (C v) t) = 2 ∨
        positiveSupport (centreQuotient (C v) t) = 3 := by
    intro v hvt
    rcases concrete_deficit_three_structure
        (C v) (by omega : 4 ≤ n)
        hdelta0 (by linarith : delta < 1)
        ht (hMin v hvt)
      with h1 | h2 | h3
    · exact Or.inl h1.1
    · exact Or.inr (Or.inl h2.1)
    · exact Or.inr (Or.inr h3.1)

  have ha12 :
      positiveSupport (centreQuotient (C a) t) = 1 ∨
      positiveSupport (centreQuotient (C a) t) = 2 := by
    rcases support12 a hat with h1 | h2 | h3
    · exact Or.inl h1
    · exact Or.inr h2
    · exact False.elim (haNot3 h3)

  have hb12 :
      positiveSupport (centreQuotient (C b) t) = 1 ∨
      positiveSupport (centreQuotient (C b) t) = 2 := by
    rcases support12 b hbt with h1 | h2 | h3
    · exact Or.inl h1
    · exact Or.inr h2
    · exact False.elim (hbNot3 h3)

  rcases ha12 with ha1 | ha2
  · rcases hb12 with hb1 | hb2
    · exfalso
      exact no_top_with_two_support_one_deficit_three
        hp hcap C hn5 hdelta0 hdeltaHalf ht hlam
        hat.symm hbt.symm hab
        hTop (hMin a hat) (hMin b hbt)
        ha1 hb1
    · exact Or.inr (Or.inl
        ⟨a,b,hat,hbt,hab,ha1,hb2⟩)
  · rcases hb12 with hb1 | hb2
    · exact Or.inr (Or.inl
        ⟨b,a,hbt,hat,hab.symm,hb1,ha2⟩)
    · exact Or.inr (Or.inr
        ⟨a,b,hat,hbt,hab,ha2,hb2⟩)

#print axioms six_point_support_multiplicity_reduction

end JSP000404Research
