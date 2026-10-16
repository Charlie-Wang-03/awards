import JSP000404Research.ResidualLossWordMultiplicityLedger
import JSP000404Research.ResidualLossTrueHoleCoverPartition
import Mathlib.Tactic

/-!
# Exact per-WORD split of global duplicate loss debt by original coverage

Each word x in the original translated loss union U contributes
multiplicity(x)-1. The U words partition into those originally
covered K and those originally uncovered (true holes within U).
This provides a word-centric complement to the exact retained-edge
source/blocker covered/uncovered triple-index event split.

No outside-U new true-hole assets are created by the partition;
the terminal six-source payment is not proved here.
-/

namespace JSP000404Research
namespace OrderedEdgeColoring

/-- Exact all-n covered/uncovered collision multiplicity split,
retaining the true multiplicity of each Boolean word. -/
theorem translatedLossDuplicateDebt_eq_word_excess_covered_plus_trueHole
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ) (choice : V → Fin n) :
    translatedLossDuplicateDebt C exponent choice =
      (Finset.sum (translatedLossCoveredWords C exponent choice)
        (fun word => lossWordMultiplicity C exponent choice word - 1)) +
      (Finset.sum (translatedLossTrueHoleWords C exponent choice)
        (fun word => lossWordMultiplicity C exponent choice word - 1)) := by
  classical
  let U := translatedLossAllCoordinateWords C exponent choice
  let K := coveredCompletionWords C
  have hpart : U = (U \ K) ∪ (U ∩ K) := by
    ext word
    simp only [Finset.mem_union, Finset.mem_sdiff, Finset.mem_inter]
    tauto
  have hdisj : Disjoint (U \ K) (U ∩ K) := by
    rw [Finset.disjoint_left]
    intro word ha hb
    exact (Finset.mem_sdiff.mp ha).2 (Finset.mem_inter.mp hb).2
  rw [translatedLossDuplicateDebt_eq_sum_wordMultiplicity_excess
    C exponent choice]
  change Finset.sum U
      (fun word => lossWordMultiplicity C exponent choice word - 1) =
    Finset.sum (U ∩ K)
      (fun word => lossWordMultiplicity C exponent choice word - 1) +
    Finset.sum (U \ K)
      (fun word => lossWordMultiplicity C exponent choice word - 1)
  conv_lhs => rw [hpart]
  rw [Finset.sum_union hdisj]
  omega

#print axioms translatedLossDuplicateDebt_eq_word_excess_covered_plus_trueHole

end OrderedEdgeColoring
end JSP000404Research
