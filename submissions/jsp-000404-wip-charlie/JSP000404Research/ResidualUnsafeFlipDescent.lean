import JSP000404Research.ResidualUnsafeSaturatedBlock
import JSP000404Research.ResidualPairFlipBlocker
import Mathlib.Tactic

/-!
# Unsafe-overlap flip descent

The genuinely hard projected-overlap case is a saturated unsafe residual pair
u < v.  Instead of flipping a coordinate active at both endpoints, choose one
retained coordinate c which is inactive at the lower endpoint u.

Unsafe overlap orientation gives the exact identity

  inactive(u) = outgoing(v) \ outgoing(u),

so c is active-outgoing at v.  If x is the unique common completion word, then
flipping c has three immediate effects:

* u does not constrain c, hence flip_c(x) stays in Q_u;
* v constrains c to false, hence flip_c(x) leaves Q_v;
* if a third cube Q_w captures flip_c(x), then c must be active at w and its
  retained bit is true, hence c is incoming at w.

There are then only two order cases.

* u < w.  Since c is inactive at u and incoming at w, c belongs to neither
  incoming(u) nor outgoing(w).  Thus c is a safe residual-recolouring target
  for the new overlap edge u--w.
* w < u.  The new overlap edge is w--u, whose upper endpoint u is strictly
  smaller than the old upper endpoint v.

Therefore one lower-inactive flip either lowers overlap multiplicity to one,
turns the defect into a safe overlap, or strictly decreases the upper endpoint
of the remaining residual overlap.  This is the well-founded descent missing
from the unsafe-saturated displacement route.
-/

namespace JSP000404Research
namespace OrderedEdgeColoring

/-- Positive exact projected budget guarantees at least one lower inactive
retained coordinate. -/
theorem retainedInactive_nonempty_of_exactProjectedBudget_pos
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    {u : V}
    (huExact : ExactProjectedBudget C exponent u)
    (huPos : 1 ≤ exponent u) :
    (retainedInactive C u).Nonempty := by
  have hfree :
      projectedFree C u = (retainedInactive C u).card := by
    unfold projectedFree
    rw [retainedInactive_card]
  have hcard :
      exponent u = (retainedInactive C u).card :=
    huExact.trans hfree
  apply Finset.card_pos.mp
  omega

/-- On an unsafe overlap, every retained coordinate inactive at the lower
endpoint is outgoing-active at the upper endpoint. -/
theorem lower_inactive_mem_upper_outgoing_of_unsafe_overlap
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    {u v : V} {base : Fin n → Bool}
    (hunsafe :
      ¬ ∃ c : Fin n, c ∉ residualForbidden C u v)
    (huBase : base ∈ retainedCompletionWords C u)
    (hvBase : base ∈ retainedCompletionWords C v)
    {c : Fin n}
    (hc : c ∈ retainedInactive C u) :
    c ∈ outgoingRetained C v := by
  have hEq :=
    retainedInactive_left_eq_outgoing_difference_of_unsafe_overlap
      C hunsafe huBase hvBase
  have hcDiff :
      c ∈ outgoingRetained C v \ outgoingRetained C u := by
    rw [← hEq]
    exact hc
  exact (Finset.mem_sdiff.mp hcDiff).1

/-- Flipping a lower-inactive coordinate of an unsafe overlap keeps the lower
cube but leaves the upper cube. -/
theorem lower_inactive_flip_stays_lower_leaves_upper
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    {u v : V} {base : Fin n → Bool}
    (hunsafe :
      ¬ ∃ c : Fin n, c ∉ residualForbidden C u v)
    (huBase : base ∈ retainedCompletionWords C u)
    (hvBase : base ∈ retainedCompletionWords C v)
    {c : Fin n}
    (hc : c ∈ retainedInactive C u) :
    flipBoolWordAt base c ∈ retainedCompletionWords C u ∧
      flipBoolWordAt base c ∉ retainedCompletionWords C v := by
  have hcInactive :
      c ∉ retainedActive C u :=
    (mem_retainedInactive C u c).1 hc
  have hcOutV :
      c ∈ outgoingRetained C v :=
    lower_inactive_mem_upper_outgoing_of_unsafe_overlap
      C hunsafe huBase hvBase hc
  have hcActiveV :
      c ∈ retainedActive C v :=
    outgoingRetained_subset_retainedActive C v hcOutV
  constructor
  · exact
      (mem_completion_iff_flip_of_inactive
        C hcInactive).2 huBase
  · exact flip_active_not_mem_completion
      C hvBase hcActiveV

/-- Any third cube blocking the lower-inactive flip activates c as an incoming
retained colour. -/
theorem lower_inactive_flip_blocker_incoming
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    {u v w : V} {base : Fin n → Bool}
    (huv : u < v)
    (hunsafe :
      ¬ ∃ c : Fin n, c ∉ residualForbidden C u v)
    (huBase : base ∈ retainedCompletionWords C u)
    (hvBase : base ∈ retainedCompletionWords C v)
    {c : Fin n}
    (hc : c ∈ retainedInactive C u)
    (huw : u ≠ w)
    (hwFlip :
      flipBoolWordAt base c ∈ retainedCompletionWords C w) :
    c ∈ incomingRetained C w := by
  have hflip :=
    lower_inactive_flip_stays_lower_leaves_upper
      C hunsafe huBase hvBase hc
  have hwv : w ≠ v := by
    intro hwv
    subst w
    exact hflip.2 hwFlip
  have hcInactiveU :
      c ∉ retainedActive C u :=
    (mem_retainedInactive C u c).1 hc
  have hcOutV :
      c ∈ outgoingRetained C v :=
    lower_inactive_mem_upper_outgoing_of_unsafe_overlap
      C hunsafe huBase hvBase hc
  have hcActiveV :
      c ∈ retainedActive C v :=
    outgoingRetained_subset_retainedActive C v hcOutV
  have hcActiveW :
      c ∈ retainedActive C w := by
    by_contra hcInactiveW
    have hwBase :
        base ∈ retainedCompletionWords C w :=
      (mem_completion_iff_flip_of_inactive
        C hcInactiveW).1 hwFlip
    exact no_three_distinct_share_retained_completion
      C (ne_of_lt huv) huw hwv
      huBase hvBase hwBase
  have hvFalse :
      retainedBit C v c = false :=
    retainedBit_false_of_outgoingRetained C hcOutV
  have hvComp :=
    (mem_retainedCompletionWords C v base).1 hvBase
  have hbaseAt :
      base c = false :=
    (hvComp c hcActiveV).trans hvFalse
  have hwComp :=
    (mem_retainedCompletionWords C w
      (flipBoolWordAt base c)).1 hwFlip
  have hwAt := hwComp c hcActiveW
  rw [flipBoolWordAt_at, hbaseAt] at hwAt
  have hwTrue :
      retainedBit C w c = true := by
    simpa using hwAt.symm
  exact
    (mem_incomingRetained_iff_retainedBit_true
      C w c).2 hwTrue

/-- A blocking third cube either creates a safe overlap to the right of u, or
creates a residual overlap whose upper endpoint has moved strictly left from
v to u. -/
theorem lower_inactive_flip_blocker_safe_or_upper_descends
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    {u v w : V} {base : Fin n → Bool}
    (huv : u < v)
    (hunsafe :
      ¬ ∃ c : Fin n, c ∉ residualForbidden C u v)
    (huBase : base ∈ retainedCompletionWords C u)
    (hvBase : base ∈ retainedCompletionWords C v)
    {c : Fin n}
    (hc : c ∈ retainedInactive C u)
    (huwNe : u ≠ w)
    (hwFlip :
      flipBoolWordAt base c ∈ retainedCompletionWords C w) :
    (u < w ∧
      IsResidual C u w ∧
      c ∉ residualForbidden C u w)
    ∨
    (w < u ∧ IsResidual C w u) := by
  have hflip :=
    lower_inactive_flip_stays_lower_leaves_upper
      C hunsafe huBase hvBase hc
  have hcInactiveU :
      c ∉ retainedActive C u :=
    (mem_retainedInactive C u c).1 hc
  have hcInW :
      c ∈ incomingRetained C w :=
    lower_inactive_flip_blocker_incoming
      C huv hunsafe huBase hvBase hc huwNe hwFlip
  rcases lt_or_gt_of_ne huwNe with huw | hwu
  · left
    have hres :
        IsResidual C u w :=
      isResidual_of_retainedCompletion_overlap_lt
        C huw hflip.1 hwFlip
    have hcNotInU :
        c ∉ incomingRetained C u := by
      intro hcIn
      exact hcInactiveU
        (incomingRetained_subset_retainedActive C u hcIn)
    have hcNotOutW :
        c ∉ outgoingRetained C w := by
      intro hcOut
      exact Finset.disjoint_left.mp
        (incomingRetained_disjoint_outgoingRetained C w)
        hcInW hcOut
    have hcSafe :
        c ∉ residualForbidden C u w := by
      unfold residualForbidden
      rw [Finset.mem_union]
      push_neg
      exact ⟨hcNotInU, hcNotOutW⟩
    exact Or.inl ⟨huw, hres, hcSafe⟩
  · right
    have hres :
        IsResidual C w u :=
      isResidual_of_retainedCompletion_overlap_lt
        C hwu hwFlip hflip.1
    exact Or.inr ⟨hwu, hres⟩

/-- Main one-step displacement package for a positive exact lower endpoint of
an unsafe overlap.

The flipped word is always retained by u and rejected by v.  It is either
globally singly covered (only by u), or a third blocker produces a safe
residual overlap, or a residual overlap with strictly smaller upper endpoint.
-/
theorem exists_lower_inactive_flip_hole_or_safe_or_upper_descends
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    {u v : V} {base : Fin n → Bool}
    (huv : u < v)
    (hunsafe :
      ¬ ∃ c : Fin n, c ∉ residualForbidden C u v)
    (huBase : base ∈ retainedCompletionWords C u)
    (hvBase : base ∈ retainedCompletionWords C v)
    (huExact : ExactProjectedBudget C exponent u)
    (huPos : 1 ≤ exponent u) :
    ∃ c : Fin n,
      c ∈ retainedInactive C u ∧
      flipBoolWordAt base c ∈ retainedCompletionWords C u ∧
      flipBoolWordAt base c ∉ retainedCompletionWords C v ∧
      (
        (∀ w : V,
          flipBoolWordAt base c ∈ retainedCompletionWords C w →
          w = u)
        ∨
        ∃ w : V,
          w ≠ u ∧
          flipBoolWordAt base c ∈ retainedCompletionWords C w ∧
          (
            (u < w ∧
              IsResidual C u w ∧
              c ∉ residualForbidden C u w)
            ∨
            (w < u ∧ IsResidual C w u)
          )
      ) := by
  classical
  obtain ⟨c, hc⟩ :=
    retainedInactive_nonempty_of_exactProjectedBudget_pos
      C exponent huExact huPos
  have hflip :=
    lower_inactive_flip_stays_lower_leaves_upper
      C hunsafe huBase hvBase hc
  refine ⟨c, hc, hflip.1, hflip.2, ?_⟩
  by_cases hblock :
      ∃ w : V,
        w ≠ u ∧
        flipBoolWordAt base c ∈ retainedCompletionWords C w
  · right
    obtain ⟨w, huw, hw⟩ := hblock
    exact ⟨w, huw, hw,
      lower_inactive_flip_blocker_safe_or_upper_descends
        C huv hunsafe huBase hvBase hc huw hw⟩
  · left
    intro w hw
    by_contra huw
    exact hblock ⟨w, huw, hw⟩

#print axioms retainedInactive_nonempty_of_exactProjectedBudget_pos
#print axioms lower_inactive_mem_upper_outgoing_of_unsafe_overlap
#print axioms lower_inactive_flip_stays_lower_leaves_upper
#print axioms lower_inactive_flip_blocker_incoming
#print axioms lower_inactive_flip_blocker_safe_or_upper_descends
#print axioms exists_lower_inactive_flip_hole_or_safe_or_upper_descends

end OrderedEdgeColoring
end JSP000404Research
