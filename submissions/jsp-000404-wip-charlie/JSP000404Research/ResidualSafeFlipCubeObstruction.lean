import JSP000404Research.ResidualCompletionCubeFlipCriterion
import JSP000404Research.RetainedOrientation
import JSP000404Research.ResidualRankedFlipTermination
import Mathlib.Tactic

/-!
# Exact completion-cube obstruction to oriented local safe flips

Suppose the lower and upper vertices a,v of a hard pair have identical
retained canonical bits. A safe retained flip at a chooses a colour c
which is OUTGOING at a and INACTIVE at v.

The flipped canonical word is outside a's retained completion cube, but
it is ALWAYS inside v's retained completion cube. Hence it is ALWAYS
globally covered. Even when no vertex has that exact canonical code,
the "code hole" outlet is a cube-only vacancy, NOT a Boolean hole.

This proves a no-go for directly charging the rank-zero local flip to
the global hole term. It does not refute JSP-000404 or imply the global
payment inequality; a different, globally coordinated payment is needed.
-/

namespace JSP000404Research
namespace OrderedEdgeColoring

/-- If a and v have the same retained canonical code, flipping any
coordinate INACTIVE at v still leaves the word inside v's completion cube. -/
theorem sameRetained_flip_mem_inactive_upper_cube
    {V : Type*} [LinearOrder V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (a v : V) (c : Fin n)
    (hsame : SameRetained C a v)
    (hcInactive : c ∉ retainedActive C v) :
    flippedRetainedCode C a c ∈ retainedCompletionWords C v := by
  apply (mem_retainedCompletionWords C v _).2
  intro d hd
  have hdc : d ≠ c := by
    intro h
    subst d
    exact hcInactive hd
  rw [flippedRetainedCode_off C a c d hdc]
  exact hsame d

/-- In fact the upper completion cube covers the flipped code even
though its own canonical retained bit DISAGREES at the inactive c. -/
theorem sameRetained_flip_upper_cube_only_disagreement
    {V : Type*} [LinearOrder V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (a v : V) (c : Fin n)
    (hsame : SameRetained C a v)
    (hcInactive : c ∉ retainedActive C v) :
    flippedRetainedCode C a c ∈ retainedCompletionWords C v ∧
      flippedRetainedCode C a c c ≠ retainedBit C v c := by
  refine ⟨sameRetained_flip_mem_inactive_upper_cube
      C a v c hsame hcInactive, ?_⟩
  intro heq
  exact (flippedRetainedCode_at_ne C a c)
    (heq.trans (hsame c).symm)

/-- The same flip cannot be a GLOBAL Boolean hole: its word is covered
at least by the upper endpoint's completion cube. -/
theorem sameRetained_flip_always_globally_covered
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (a v : V) (c : Fin n)
    (hsame : SameRetained C a v)
    (hcInactive : c ∉ retainedActive C v) :
    flippedRetainedCode C a c ∈ coveredCompletionWords C := by
  apply (mem_coveredCompletionWords C _).2
  refine ⟨v, ?_⟩
  exact (mem_completionFibre C _ v).2
    (sameRetained_flip_mem_inactive_upper_cube C a v c
      hsame hcInactive)

/-- Flipping an OUTGOING retained colour at the lower endpoint leaves
the lower endpoint's own completion cube. This is a local exit only. -/
theorem outgoing_flip_exits_lower_completion_cube
    {V : Type*} [LinearOrder V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (a : V) (c : Fin n)
    (hcOutgoing : c ∈ outgoingRetained C a) :
    flippedRetainedCode C a c ∉ retainedCompletionWords C a := by
  have hcActive : c ∈ retainedActive C a := by
    rw [retainedActive_eq_incoming_union_outgoing C a]
    exact Finset.mem_union.mpr (Or.inr hcOutgoing)
  have hbase :
      (fun d => retainedBit C a d) ∈
        retainedCompletionWords C a := by
    apply (mem_retainedCompletionWords C a _).2
    intro d _
    rfl
  have hflip :=
    flip_active_not_mem_completion C hbase hcActive
  change flippedRetainedCode C a c ∉
    retainedCompletionWords C a at hflip
  exact hflip

/-- The precise two-cube migration of any oriented safe flip on a
same-retained pair. This rules out a direct global-hole charge. -/
theorem oriented_safe_flip_migrates_cubes_not_global_hole
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (a v : V) (c : Fin n)
    (hsame : SameRetained C a v)
    (hcOutgoing : c ∈ outgoingRetained C a)
    (hcInactive : c ∉ retainedActive C v) :
    flippedRetainedCode C a c ∉ retainedCompletionWords C a ∧
      flippedRetainedCode C a c ∈ retainedCompletionWords C v ∧
      flippedRetainedCode C a c ∈ coveredCompletionWords C := by
  exact ⟨
    outgoing_flip_exits_lower_completion_cube C a c hcOutgoing,
    sameRetained_flip_mem_inactive_upper_cube C a v c hsame hcInactive,
    sameRetained_flip_always_globally_covered C a v c hsame hcInactive⟩

/-- Even if no actual vertex realizes the flipped canonical code, it
is still covered by the upper endpoint: canonical vacancy is not a hole. -/
theorem oriented_safe_flip_code_vacancy_not_global_hole
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (a v : V) (c : Fin n)
    (hsame : SameRetained C a v)
    (hcInactive : c ∉ retainedActive C v)
    (_hcodeVacant :
      ¬ ∃ w : V, (fun d => retainedBit C w d) =
        flippedRetainedCode C a c) :
    flippedRetainedCode C a c ∈ coveredCompletionWords C :=
  sameRetained_flip_always_globally_covered C a v c hsame hcInactive

/-- At zero retained colour rank the strictly descending exterior
blocker is impossible. Nonetheless the first surviving outlet is only a
canonical-code vacancy, and its Boolean word is PROVABLY covered by v's
completion cube. The other outlet is a locally separated residual edge.

This connects the ranked-descent result to the actual completion-cube
accounting obstruction, rather than confusing the two notions of hole. -/
theorem zero_rank_safe_flip_cannot_pay_boolean_hole
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (a v : V) (c : Fin n)
    (hzero : c.val = 0)
    (hsame : SameRetained C a v)
    (hcInactive : c ∉ retainedActive C v)
    (houtlet :
      (¬ ∃ w : V,
        (fun d => retainedBit C w d) = flippedRetainedCode C a c) ∨
      (∃ w : V,
        a < w ∧ w < v ∧
        IsResidual C w v ∧ RetainedSeparated C w v) ∨
      (∃ w : V,
        v < w ∧
        (fun d => retainedBit C w d) = flippedRetainedCode C a c ∧
        (C.color v w).val < c.val)) :
    flippedRetainedCode C a c ∈ coveredCompletionWords C ∧
      ((¬ ∃ w : V,
        (fun d => retainedBit C w d) = flippedRetainedCode C a c) ∨
      (∃ w : V,
        a < w ∧ w < v ∧
        IsResidual C w v ∧ RetainedSeparated C w v)) := by
  constructor
  · exact sameRetained_flip_always_globally_covered
      C a v c hsame hcInactive
  · exact zero_colour_flip_code_hole_or_separation
      C a v c hzero houtlet

#print axioms zero_rank_safe_flip_cannot_pay_boolean_hole

#print axioms sameRetained_flip_mem_inactive_upper_cube
#print axioms sameRetained_flip_upper_cube_only_disagreement
#print axioms sameRetained_flip_always_globally_covered
#print axioms outgoing_flip_exits_lower_completion_cube
#print axioms oriented_safe_flip_migrates_cubes_not_global_hole
#print axioms oriented_safe_flip_code_vacancy_not_global_hole

end OrderedEdgeColoring
end JSP000404Research
