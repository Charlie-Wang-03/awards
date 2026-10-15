import JSP000404Research.ResidualLossCoveredPairBudget
import Mathlib.Tactic

/-!
# Exact chosen-coordinate blocker-carrier representation of covered loss

Unlike the earlier inclusive upper bound by *all* genuine blocker triples,
this module retains the source's **actually chosen** active flip coordinate.

For any active loss choice, the set of globally covered translated-loss
Boolean words is EXACTLY the union of concrete source/blocker/chosen-coordinate
intersections, where the source and blocker have opposite retained bits.

Different triples are NOT claimed disjoint. The equality is an exact
set-level localization of an otherwise abstract global payment debt.
It does not close the remaining global true-hole/surplus payment inequality.
-/

namespace JSP000404Research
namespace OrderedEdgeColoring

noncomputable def chosenLossCoveredBlockerTriples
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (choice : V → Fin n) : Finset ((V × V) × Fin n) := by
  classical
  exact Finset.univ.filter (fun z =>
    z.1.1 ∈ projectedLossVertices C exponent ∧
    z.1.1 ≠ z.1.2 ∧
    choice z.1.1 = z.2 ∧
    z.2 ∈ retainedActive C z.1.1 ∧
    z.2 ∈ retainedActive C z.1.2 ∧
    retainedBit C z.1.2 z.2 = !(retainedBit C z.1.1 z.2))

theorem translatedLossCovered_eq_chosenTriple_union
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexp : ∀ v, exponent v ≤ n)
    (honeLoss :
      ∀ v, (active C v).card ≤ n - exponent v + 1)
    (choice : V → Fin n)
    (hchoice : ∀ v ∈ projectedLossVertices C exponent,
      choice v ∈ retainedActive C v) :
    translatedLossCoveredWords C exponent choice =
      (chosenLossCoveredBlockerTriples C exponent choice).biUnion
        (lossCoveredBlockerTripleWords C) := by
  classical
  apply Finset.Subset.antisymm
  · intro word hcovered
    have hpair := Finset.mem_inter.mp hcovered
    have hU := hpair.1
    have hK := hpair.2
    change word ∈ (Finset.univ : Finset (Fin n)).biUnion
      (fun c => translatedLossSliceWords C exponent choice c) at hU
    obtain ⟨c, _, hSlice⟩ := Finset.mem_biUnion.mp hU
    change word ∈ (lossCoordinateSlice C exponent choice c).biUnion
      (fun v => translatedCompletionWords C v c) at hSlice
    obtain ⟨v, hvSlice, hvWord⟩ := Finset.mem_biUnion.mp hSlice
    have hvData :=
      (mem_lossCoordinateSlice C exponent choice c v).1 hvSlice
    have hvLoss := hvData.1
    have hvc : choice v = c := hvData.2
    have hcActive : c ∈ retainedActive C v := by
      rw [← hvc]
      exact hchoice v hvLoss
    obtain ⟨w, hwFibre⟩ :=
      (mem_coveredCompletionWords C word).1 hK
    have hwBlock : word ∈ retainedCompletionWords C w :=
      (mem_completionFibre C word w).1 hwFibre
    have hvneq : v ≠ w := by
      intro heq
      subst w
      have hdisj :=
        translatedCompletionWords_disjoint_original_of_active
          C hcActive
      exact Finset.disjoint_left.mp hdisj hvWord hwBlock
    have hsource :
        flipBoolWordAt word c ∈ retainedCompletionWords C v :=
      (mem_translatedCompletionWords C v c word).1 hvWord
    have hdest :
        flipBoolWordAt (flipBoolWordAt word c) c ∈
          retainedCompletionWords C w := by
      simpa only [flipBoolWordAt_involutive] using hwBlock
    have hcBlocked :=
      loss_translated_blocker_active C exponent hexp honeLoss
        hvLoss hcActive hvneq hsource hdest
    have hop :=
      loss_translated_blocker_bit_opposite
        C exponent hexp honeLoss
        hvLoss hcActive hvneq hsource hdest
    apply Finset.mem_biUnion.mpr
    refine ⟨((v, w), c), ?_, ?_⟩
    · simp only [chosenLossCoveredBlockerTriples,
        Finset.mem_filter, Finset.mem_univ, true_and,
        Prod.fst, Prod.snd]
      exact ⟨hvLoss, hvneq, hvc, hcActive, hcBlocked, hop⟩
    · exact Finset.mem_inter.mpr ⟨hvWord, hwBlock⟩
  · intro word hword
    obtain ⟨((v, w), c), hTriple, hInter⟩ :=
      Finset.mem_biUnion.mp hword
    have hdata :
        v ∈ projectedLossVertices C exponent ∧
        v ≠ w ∧ choice v = c ∧
        c ∈ retainedActive C v ∧
        c ∈ retainedActive C w ∧
        retainedBit C w c = !(retainedBit C v c) := by
      exact (Finset.mem_filter.mp hTriple).2
    have hTV :
        word ∈ translatedCompletionWords C v c :=
      (Finset.mem_inter.mp hInter).1
    have hQ :
        word ∈ retainedCompletionWords C w :=
      (Finset.mem_inter.mp hInter).2
    have hvSlice :
        v ∈ lossCoordinateSlice C exponent choice c :=
      (mem_lossCoordinateSlice C exponent choice c v).2
        ⟨hdata.1, hdata.2.2.1⟩
    have hSlice :
        word ∈ translatedLossSliceWords C exponent choice c :=
      Finset.mem_biUnion.mpr ⟨v, hvSlice, hTV⟩
    have hU :
        word ∈ translatedLossAllCoordinateWords C exponent choice :=
      Finset.mem_biUnion.mpr ⟨c, Finset.mem_univ _, hSlice⟩
    have hK :
        word ∈ coveredCompletionWords C := by
      apply (mem_coveredCompletionWords C word).2
      exact ⟨w, (mem_completionFibre C word w).2 hQ⟩
    exact Finset.mem_inter.mpr ⟨hU, hK⟩

/-- A sharper (chosen-coordinate) triple-mass upper bound; still a
sum of possibly overlapping intersections, not a true-hole credit. -/
theorem translatedLossCovered_card_le_chosenTriple_mass
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexp : ∀ v, exponent v ≤ n)
    (honeLoss :
      ∀ v, (active C v).card ≤ n - exponent v + 1)
    (choice : V → Fin n)
    (hchoice : ∀ v ∈ projectedLossVertices C exponent,
      choice v ∈ retainedActive C v) :
    (translatedLossCoveredWords C exponent choice).card ≤
      ∑ z ∈ chosenLossCoveredBlockerTriples C exponent choice,
        (lossCoveredBlockerTripleWords C z).card := by
  classical
  rw [translatedLossCovered_eq_chosenTriple_union
    C exponent hexp honeLoss choice hchoice]
  exact Finset.card_biUnion_le

#print axioms translatedLossCovered_eq_chosenTriple_union
#print axioms translatedLossCovered_card_le_chosenTriple_mass

end OrderedEdgeColoring
end JSP000404Research
