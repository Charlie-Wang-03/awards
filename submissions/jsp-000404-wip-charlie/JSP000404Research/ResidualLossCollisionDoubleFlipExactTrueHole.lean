import JSP000404Research.ResidualLossCollisionDoubleFlipCrossActivity
import Mathlib.Tactic

/-!
# Exact ORIGINAL-SOURCE criterion for double-flip collision TRUE holes

For a REAL earliest-loss-coordinate collision with original owners
v=p.1 and u=p.2, and different chosen flip coordinates c,d, the
unique remaining local hole candidate is the opposite Boolean corner

  q := flip(flip(word,c),d).

We prove q belongs to TRUE holes OUTSIDE ALL translated loss words IFF
ALL of the following independently checkable ORIGINAL-PLANE coding
conditions hold:

(1) d is genuinely retained-ACTIVE at the c-source owner v;
(2) c is genuinely retained-ACTIVE at the d-source owner u;
(3) NO third-party original retained cube contains q;
(4) q belongs to NO translated-loss slice (including other choices).

The backward implication is nontrivial: these conditions exclude q
from BOTH original source cubes via active-bit flips, and all remaining
third-party cubes via explicit geometric exclusion. The forward
implication forces opposite cross-activity by source-native ancestry.

This is an exact local characterization, not the unproved assertion
that every collision produces such a hole. GLOBAL nonreusing allocation
across many collisions and the five other debt classes remains OPEN.
-/

namespace JSP000404Research
namespace OrderedEdgeColoring

/-- Precise necessary AND sufficient actual retained-cube test for an
opposite two-bit loss-collision word to be an eligible EXTERIOR true hole.
Unlike mere cardinality bounds, no potential third-party cover and no
translated-loss reuse is silently discarded. -/
theorem actual_loss_collision_double_flip_external_hole_iff
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ) (choice : V → Fin n)
    {c d : Fin n} (hcd : c ≠ d)
    (p : V × V)
    (hp : p ∈ crossLossConflictPairs C exponent choice c d)
    {word : Fin n → Bool}
    (hw : word ∈ lossEarliestActualEdgeCarrier
      C exponent choice c d p) :
    let q := flipBoolWordAt (flipBoolWordAt word c) d
    q ∈ lossLedgerOutsideTranslatedTrueHoles C exponent choice ↔
      d ∈ retainedActive C p.1 ∧
      c ∈ retainedActive C p.2 ∧
      (∀ z : V, z ≠ p.1 → z ≠ p.2 →
        q ∉ retainedCompletionWords C z) ∧
      q ∉ translatedLossAllCoordinateWords C exponent choice := by
  classical
  dsimp only
  let q := flipBoolWordAt (flipBoolWordAt word c) d
  change q ∈ lossLedgerOutsideTranslatedTrueHoles C exponent choice ↔
    d ∈ retainedActive C p.1 ∧
    c ∈ retainedActive C p.2 ∧
    (∀ z : V, z ≠ p.1 → z ≠ p.2 →
      q ∉ retainedCompletionWords C z) ∧
    q ∉ translatedLossAllCoordinateWords C exponent choice
  constructor
  · intro hq
    have hcross :=
      actual_loss_collision_double_flip_external_hole_forces_cross_activity
        C exponent choice hcd p hp hw hq
    refine ⟨hcross.1,hcross.2,?_,(Finset.mem_sdiff.mp hq).2⟩
    intro z hz1 hz2 hzMember
    have hcovered : q ∈ coveredCompletionWords C :=
      (mem_coveredCompletionWords C q).2
        ⟨z,(mem_completionFibre C q z).2 hzMember⟩
    exact (Finset.mem_sdiff.mp
      (Finset.mem_sdiff.mp hq).1).2 hcovered
  · rintro ⟨hcrossV,hcrossU,hthird,hnotLoss⟩
    obtain ⟨_,hvSource,huSource,_⟩ :=
      lossEarliestActualEdgeCarrier_two_distinct_owner_ancestors
        C exponent choice hcd p hp hw
    have hnotV : q ∉ retainedCompletionWords C p.1 :=
      flip_active_not_mem_completion C hvSource hcrossV
    have hnotU' :
        flipBoolWordAt (flipBoolWordAt word d) c ∉
          retainedCompletionWords C p.2 :=
      flip_active_not_mem_completion C huSource hcrossU
    have hnotU : q ∉ retainedCompletionWords C p.2 := by
      simpa only [q, flipBoolWordAt_commute word hcd] using hnotU'
    have hnotCovered : q ∉ coveredCompletionWords C := by
      intro hcovered
      obtain ⟨z,hfib⟩ := (mem_coveredCompletionWords C q).1 hcovered
      have hmem := (mem_completionFibre C q z).1 hfib
      by_cases hz1 : z = p.1
      · subst z
        exact hnotV hmem
      by_cases hz2 : z = p.2
      · subst z
        exact hnotU hmem
      exact hthird z hz1 hz2 hmem
    have hglobal : q ∈ lossLedgerGlobalTrueHoles C :=
      Finset.mem_sdiff.mpr ⟨Finset.mem_univ _,hnotCovered⟩
    exact Finset.mem_sdiff.mpr ⟨hglobal,hnotLoss⟩

#print axioms actual_loss_collision_double_flip_external_hole_iff

end OrderedEdgeColoring
end JSP000404Research
