import JSP000404Research.ResidualLossEarliestEdgeTwoOwnerCorners
import JSP000404Research.ResidualLossExternalHoleBudget
import Mathlib.Tactic

/-!
# Exact third-party cover obstruction of an active real-edge collision

An actual earliest-coordinate cross-loss collision word x has two
different original completion-cube owners v,w of its covered one-flip
ancestors. If both chosen flip coordinates are genuinely retained-active,
x itself belongs to NEITHER owner's original cube.

Consequently x is globally covered IFF it belongs to a DIFFERENT
third-party vertex's original cube. Dually, x is a genuine GLOBAL
hole IFF every third-party retained cube excludes it.

This is an exact, source-native characterization: it does NOT imply
the third-party condition holds, and does NOT make x an outside-loss
hole. The global six-source payment remains unproved.
-/

namespace JSP000404Research
namespace OrderedEdgeColoring

/-- For an active first-hit cross-loss collision, any actual ORIGINAL
covering owner must be neither of the two edge-carrier endpoints. -/
theorem lossEarliestActualEdgeCarrier_covered_iff_third_owner
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ) (choice : V → Fin n)
    (hchoice : ∀ v ∈ projectedLossVertices C exponent,
      choice v ∈ retainedActive C v)
    {c d : Fin n} (p : V × V)
    (hp : p ∈ crossLossConflictPairs C exponent choice c d)
    {word : Fin n → Bool}
    (hw : word ∈ lossEarliestActualEdgeCarrier
      C exponent choice c d p) :
    word ∈ coveredCompletionWords C ↔
      ∃ u : V,
        u ≠ p.1 ∧ u ≠ p.2 ∧
          word ∈ retainedCompletionWords C u := by
  classical
  have hnot :=
    lossEarliestActualEdgeCarrier_outside_both_owner_cubes
      C exponent choice hchoice p hp hw
  constructor
  · intro hc
    obtain ⟨u, hFibre⟩ :=
      (mem_coveredCompletionWords C word).1 hc
    have hu : word ∈ retainedCompletionWords C u :=
      (mem_completionFibre C word u).1 hFibre
    refine ⟨u, ?_, ?_, hu⟩
    · intro heq
      exact hnot.1 (by simpa [heq] using hu)
    · intro heq
      exact hnot.2 (by simpa [heq] using hu)
  · rintro ⟨u, _hu1, _hu2, hu⟩
    exact (mem_coveredCompletionWords C word).2
      ⟨u, (mem_completionFibre C word u).2 hu⟩

/-- For an active true cross-loss collision, absence of THIRD-PARTY
owners is exactly the condition for the word itself to be globally
uncovered. This is a GLOBAL true hole, NOT necessarily an
outside-translated-loss true hole (in fact it belongs to that union). -/
theorem lossEarliestActualEdgeCarrier_trueHole_iff_no_third_owner
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ) (choice : V → Fin n)
    (hchoice : ∀ v ∈ projectedLossVertices C exponent,
      choice v ∈ retainedActive C v)
    {c d : Fin n} (p : V × V)
    (hp : p ∈ crossLossConflictPairs C exponent choice c d)
    {word : Fin n → Bool}
    (hw : word ∈ lossEarliestActualEdgeCarrier
      C exponent choice c d p) :
    word ∈ lossLedgerGlobalTrueHoles C ↔
      ¬ ∃ u : V,
        u ≠ p.1 ∧ u ≠ p.2 ∧
          word ∈ retainedCompletionWords C u := by
  classical
  have hiff :=
    lossEarliestActualEdgeCarrier_covered_iff_third_owner
      C exponent choice hchoice p hp hw
  constructor
  · intro hhole hthird
    have hcovered := hiff.mpr hthird
    exact (Finset.mem_sdiff.mp hhole).2 hcovered
  · intro hno
    apply Finset.mem_sdiff.mpr
    refine ⟨Finset.mem_univ word, ?_⟩
    intro hcovered
    exact hno (hiff.mp hcovered)

#print axioms lossEarliestActualEdgeCarrier_covered_iff_third_owner
#print axioms lossEarliestActualEdgeCarrier_trueHole_iff_no_third_owner

end OrderedEdgeColoring
end JSP000404Research
