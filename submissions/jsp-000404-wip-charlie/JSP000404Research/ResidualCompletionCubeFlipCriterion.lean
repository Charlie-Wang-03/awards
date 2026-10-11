import JSP000404Research.ResidualCompletionAccounting
import JSP000404Research.ResidualHoleInjection
import JSP000404Research.BooleanFlipCore
import Mathlib.Tactic

/-!
# Safe flips: canonical code holes versus global completion holes

A flipped vertex code is not automatically uncovered. A second vertex can
contain that Boolean word in its completion CUBE without realizing the exact
canonical code. These lemmas record the precise missing active-coordinate
separation, without claiming the unresolved global payment inequality.

No additional geometric or Hall assumption is silently inserted.
-/

namespace JSP000404Research
namespace OrderedEdgeColoring

/-- If c is inactive at a potential cube blocker w, the unflipped code
and its one-coordinate flip have EXACTLY THE SAME membership in w's cube.
This exposes why rank-zero canonical-code vacancy need not pay a global hole. -/
theorem flippedRetainedCode_mem_cube_iff_base_of_inactive
    {V : Type*} [LinearOrder V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (a w : V) (c : Fin n)
    (hc : c ∉ retainedActive C w) :
    flippedRetainedCode C a c ∈ retainedCompletionWords C w ↔
      (fun d => retainedBit C a d) ∈ retainedCompletionWords C w := by
  have heq :
      flippedRetainedCode C a c =
        flipBoolWordAt (fun d => retainedBit C a d) c := rfl
  rw [heq]
  exact mem_retainedCompletionWords_flip_iff_of_inactive C hc

/-- A *global* hole is equivalent to an active-coordinate separation
witness against EVERY vertex completion cube. Mere inequality from each
vertex's full canonical code is strictly weaker. -/
theorem flippedRetainedCode_global_hole_iff_active_separator
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (a : V) (c : Fin n) :
    flippedRetainedCode C a c ∉ coveredCompletionWords C ↔
      ∀ w : V, ∃ d : Fin n,
        d ∈ retainedActive C w ∧
        flippedRetainedCode C a c d ≠ retainedBit C w d := by
  classical
  have hcover :
      flippedRetainedCode C a c ∈ coveredCompletionWords C ↔
        ∃ w : V, flippedRetainedCode C a c ∈ retainedCompletionWords C w := by
    rw [mem_coveredCompletionWords]
    constructor
    · rintro ⟨w, hw⟩
      exact ⟨w, (mem_completionFibre C _ w).1 hw⟩
    · rintro ⟨w, hw⟩
      exact ⟨w, (mem_completionFibre C _ w).2 hw⟩
  constructor
  · intro hhole w
    by_contra hno
    push Not at hno
    have hw : flippedRetainedCode C a c ∈ retainedCompletionWords C w := by
      apply (mem_retainedCompletionWords C w _).2
      intro d hd
      exact hno d hd
    exact hhole (hcover.mpr ⟨w, hw⟩)
  · intro hsep hcovered
    obtain ⟨w, hw⟩ := hcover.mp hcovered
    obtain ⟨d, hd, hne⟩ := hsep w
    exact hne ((mem_retainedCompletionWords C w _).1 hw d hd)

/-- An occupied completion word whose exact flipped CANONICAL CODE is
unrealized must be covered by some other vertex solely through a retained
INACTIVE coordinate: the vertex agrees on every active coordinate but differs
on at least one inactive coordinate. This isolates the genuine cube-only
blocker which the rank descent trichotomy does not address. -/
theorem code_hole_covered_has_inactive_disagreement
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (a : V) (c : Fin n)
    (hcodehole :
      ¬ ∃ w : V, (fun d => retainedBit C w d) =
        flippedRetainedCode C a c)
    (hcovered :
      flippedRetainedCode C a c ∈ coveredCompletionWords C) :
    ∃ w : V, ∃ d : Fin n,
      flippedRetainedCode C a c ∈ retainedCompletionWords C w ∧
      d ∉ retainedActive C w ∧
      flippedRetainedCode C a c d ≠ retainedBit C w d := by
  classical
  obtain ⟨w, hfw⟩ :=
    (mem_coveredCompletionWords C _).1 hcovered
  have hwcube :
      flippedRetainedCode C a c ∈ retainedCompletionWords C w :=
    (mem_completionFibre C _ w).1 hfw
  have hneq :
      (fun d => retainedBit C w d) ≠
        flippedRetainedCode C a c := by
    intro heq
    exact hcodehole ⟨w, heq⟩
  have hdiff :
      ∃ d : Fin n,
        retainedBit C w d ≠ flippedRetainedCode C a c d := by
    by_contra hnone
    push Not at hnone
    apply hneq
    funext d
    exact hnone d
  obtain ⟨d, hdiff⟩ := hdiff
  have hinactive : d ∉ retainedActive C w := by
    intro hd
    have heq :=
      (mem_retainedCompletionWords C w _).1 hwcube d hd
    exact hdiff heq.symm
  exact ⟨w, d, hwcube, hinactive, hdiff.symm⟩

/-- Canonical-code vacancy WOULD imply a global hole if every vertex fixed
all retained coordinates. The full-activity premise is deliberately explicit:
it is not available for the general JSP-000404 lower branch. -/
theorem canonical_code_hole_global_of_full_retained_active
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (a : V) (c : Fin n)
    (hfull : ∀ w : V, retainedActive C w = Finset.univ)
    (hcodehole :
      ¬ ∃ w : V, (fun d => retainedBit C w d) =
        flippedRetainedCode C a c) :
    flippedRetainedCode C a c ∉ coveredCompletionWords C := by
  apply (flippedRetainedCode_global_hole_iff_active_separator C a c).2
  intro w
  by_contra hno
  push Not at hno
  have heq :
      (fun d => retainedBit C w d) =
        flippedRetainedCode C a c := by
    funext d
    have hd : d ∈ retainedActive C w := by
      rw [hfull w]
      simp
    exact (hno d hd).symm
  exact hcodehole ⟨w, heq⟩

#print axioms flippedRetainedCode_mem_cube_iff_base_of_inactive
#print axioms flippedRetainedCode_global_hole_iff_active_separator
#print axioms code_hole_covered_has_inactive_disagreement
#print axioms canonical_code_hole_global_of_full_retained_active

end OrderedEdgeColoring
end JSP000404Research
