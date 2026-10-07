import JSP000404Research.ResidualUnsafeFlipDescent
import Mathlib.Tactic

/-!
# Symmetric unsafe-overlap flip descent from the upper endpoint

ResidualUnsafeFlipDescent treats a positive exact lower endpoint.  The upper
endpoint has a dual outlet.

For an unsafe overlap u<v, every retained coordinate inactive at v belongs to

  incoming(u) \ incoming(v).

Thus flipping such a coordinate keeps the word in Q_v and removes it from
Q_u.  Any third blocker w must constrain the flipped coordinate to false, so
that coordinate is outgoing at w.

The order case v<w is impossible: the new overlap v--w would be residual and
would form a monochromatic residual two-path u--v--w with the original
residual edge.  Hence every blocker satisfies w<v.  Since the flipped
coordinate is outgoing at w and inactive at v, it avoids

  incoming(w) union outgoing(v),

and is therefore a safe recolouring coordinate for the new residual pair
w--v.

Consequently a positive exact upper endpoint also displaces an unsafe overlap
either to a singly-covered word or immediately to a safe residual overlap.
Together with the lower-endpoint result, the only unsafe saturated carriers
not covered by a one-step safe descent are the zero--zero exponent carriers.
-/

namespace JSP000404Research
namespace OrderedEdgeColoring

/-- Positive exact projected budget at the upper endpoint supplies an inactive
retained coordinate. -/
theorem retainedInactive_nonempty_of_exactProjectedBudget_pos_upper
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    {v : V}
    (hvExact : ExactProjectedBudget C exponent v)
    (hvPos : 1 ≤ exponent v) :
    (retainedInactive C v).Nonempty :=
  retainedInactive_nonempty_of_exactProjectedBudget_pos
    C exponent hvExact hvPos

/-- On an unsafe overlap, every coordinate inactive at the upper endpoint is
incoming-active at the lower endpoint. -/
theorem upper_inactive_mem_lower_incoming_of_unsafe_overlap
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    {u v : V} {base : Fin n → Bool}
    (hunsafe :
      ¬ ∃ c : Fin n, c ∉ residualForbidden C u v)
    (huBase : base ∈ retainedCompletionWords C u)
    (hvBase : base ∈ retainedCompletionWords C v)
    {c : Fin n}
    (hc : c ∈ retainedInactive C v) :
    c ∈ incomingRetained C u := by
  have hEq :=
    retainedInactive_right_eq_incoming_difference_of_unsafe_overlap
      C hunsafe huBase hvBase
  have hcDiff :
      c ∈ incomingRetained C u \ incomingRetained C v := by
    rw [← hEq]
    exact hc
  exact (Finset.mem_sdiff.mp hcDiff).1

/-- Flipping an upper-inactive coordinate keeps the upper cube and leaves the
lower cube. -/
theorem upper_inactive_flip_stays_upper_leaves_lower
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    {u v : V} {base : Fin n → Bool}
    (hunsafe :
      ¬ ∃ c : Fin n, c ∉ residualForbidden C u v)
    (huBase : base ∈ retainedCompletionWords C u)
    (hvBase : base ∈ retainedCompletionWords C v)
    {c : Fin n}
    (hc : c ∈ retainedInactive C v) :
    flipBoolWordAt base c ∈ retainedCompletionWords C v ∧
      flipBoolWordAt base c ∉ retainedCompletionWords C u := by
  have hcInactiveV :
      c ∉ retainedActive C v :=
    (mem_retainedInactive C v c).1 hc
  have hcInU :
      c ∈ incomingRetained C u :=
    upper_inactive_mem_lower_incoming_of_unsafe_overlap
      C hunsafe huBase hvBase hc
  have hcActiveU :
      c ∈ retainedActive C u :=
    incomingRetained_subset_retainedActive C u hcInU
  constructor
  · exact
      (mem_completion_iff_flip_of_inactive
        C hcInactiveV).2 hvBase
  · exact flip_active_not_mem_completion
      C huBase hcActiveU

/-- A third blocker of the upper-inactive flip activates c as an outgoing
retained colour. -/
theorem upper_inactive_flip_blocker_outgoing
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    {u v w : V} {base : Fin n → Bool}
    (huv : u < v)
    (hunsafe :
      ¬ ∃ c : Fin n, c ∉ residualForbidden C u v)
    (huBase : base ∈ retainedCompletionWords C u)
    (hvBase : base ∈ retainedCompletionWords C v)
    {c : Fin n}
    (hc : c ∈ retainedInactive C v)
    (hvw : v ≠ w)
    (hwFlip :
      flipBoolWordAt base c ∈ retainedCompletionWords C w) :
    c ∈ outgoingRetained C w := by
  have hflip :=
    upper_inactive_flip_stays_upper_leaves_lower
      C hunsafe huBase hvBase hc
  have huw : u ≠ w := by
    intro huw
    subst w
    exact hflip.2 hwFlip
  have hcInactiveV :
      c ∉ retainedActive C v :=
    (mem_retainedInactive C v c).1 hc
  have hcInU :
      c ∈ incomingRetained C u :=
    upper_inactive_mem_lower_incoming_of_unsafe_overlap
      C hunsafe huBase hvBase hc
  have hcActiveU :
      c ∈ retainedActive C u :=
    incomingRetained_subset_retainedActive C u hcInU
  have hcActiveW : c ∈ retainedActive C w := by
    by_contra hcInactiveW
    have hwBase :
        base ∈ retainedCompletionWords C w :=
      (mem_completion_iff_flip_of_inactive
        C hcInactiveW).1 hwFlip
    exact no_three_distinct_share_retained_completion
      C (ne_of_lt huv) huw hvw
      huBase hvBase hwBase
  have huTrue :
      retainedBit C u c = true :=
    (mem_incomingRetained_iff_retainedBit_true
      C u c).1 hcInU
  have huComp :=
    (mem_retainedCompletionWords C u base).1 huBase
  have hbaseAt :
      base c = true :=
    (huComp c hcActiveU).trans huTrue
  have hwComp :=
    (mem_retainedCompletionWords C w
      (flipBoolWordAt base c)).1 hwFlip
  have hwAt := hwComp c hcActiveW
  rw [flipBoolWordAt_at, hbaseAt] at hwAt
  have hwFalse :
      retainedBit C w c = false := by
    simpa using hwAt.symm
  rw [retainedActive_eq_incoming_union_outgoing C w] at hcActiveW
  rcases Finset.mem_union.mp hcActiveW with hIn | hOut
  · have hwTrue :
        retainedBit C w c = true :=
      (mem_incomingRetained_iff_retainedBit_true
        C w c).1 hIn
    rw [hwFalse] at hwTrue
    contradiction
  · exact hOut

/-- Every blocker of the upper-inactive flip lies strictly to the left of v
and creates a safe residual overlap w--v. -/
theorem upper_inactive_flip_blocker_is_safe_to_left
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    {u v w : V} {base : Fin n → Bool}
    (huv : u < v)
    (hunsafe :
      ¬ ∃ c : Fin n, c ∉ residualForbidden C u v)
    (huBase : base ∈ retainedCompletionWords C u)
    (hvBase : base ∈ retainedCompletionWords C v)
    {c : Fin n}
    (hc : c ∈ retainedInactive C v)
    (hvwNe : v ≠ w)
    (hwFlip :
      flipBoolWordAt base c ∈ retainedCompletionWords C w) :
    w < v ∧
      IsResidual C w v ∧
      c ∉ residualForbidden C w v := by
  have hflip :=
    upper_inactive_flip_stays_upper_leaves_lower
      C hunsafe huBase hvBase hc
  have hcInactiveV :
      c ∉ retainedActive C v :=
    (mem_retainedInactive C v c).1 hc
  have hcOutW :
      c ∈ outgoingRetained C w :=
    upper_inactive_flip_blocker_outgoing
      C huv hunsafe huBase hvBase hc hvwNe hwFlip
  rcases lt_or_gt_of_ne hvwNe.symm with hwv | hvw
  · have hres :
        IsResidual C w v :=
      isResidual_of_retainedCompletion_overlap_lt
        C hwv hwFlip hflip.1
    have hcNotInW :
        c ∉ incomingRetained C w := by
      intro hIn
      exact Finset.disjoint_left.mp
        (incomingRetained_disjoint_outgoingRetained C w)
        hIn hcOutW
    have hcNotOutV :
        c ∉ outgoingRetained C v := by
      intro hOut
      exact hcInactiveV
        (outgoingRetained_subset_retainedActive C v hOut)
    have hcSafe :
        c ∉ residualForbidden C w v := by
      unfold residualForbidden
      rw [Finset.mem_union]
      push_neg
      exact ⟨hcNotInW, hcNotOutV⟩
    exact ⟨hwv, hres, hcSafe⟩
  · have hresVW :
        IsResidual C v w :=
      isResidual_of_retainedCompletion_overlap_lt
        C hvw hflip.1 hwFlip
    have hresUV :
        IsResidual C u v :=
      isResidual_of_retainedCompletion_overlap_lt
        C huv huBase hvBase
    exact False.elim
      (no_two_residual_on_path C huv hvw hresUV hresVW)

/-- Strong symmetric one-step outlet from a positive exact upper endpoint. -/
theorem exists_upper_inactive_flip_single_or_safe_overlap
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    {u v : V} {base : Fin n → Bool}
    (huv : u < v)
    (hunsafe :
      ¬ ∃ c : Fin n, c ∉ residualForbidden C u v)
    (huBase : base ∈ retainedCompletionWords C u)
    (hvBase : base ∈ retainedCompletionWords C v)
    (hvExact : ExactProjectedBudget C exponent v)
    (hvPos : 1 ≤ exponent v) :
    ∃ c : Fin n,
      c ∈ retainedInactive C v ∧
      flipBoolWordAt base c ∈ retainedCompletionWords C v ∧
      flipBoolWordAt base c ∉ retainedCompletionWords C u ∧
      (
        (∀ w : V,
          flipBoolWordAt base c ∈ retainedCompletionWords C w →
          w = v)
        ∨
        ∃ w : V,
          w ≠ v ∧
          flipBoolWordAt base c ∈ retainedCompletionWords C w ∧
          w < v ∧
          IsResidual C w v ∧
          c ∉ residualForbidden C w v
      ) := by
  classical
  obtain ⟨c, hc⟩ :=
    retainedInactive_nonempty_of_exactProjectedBudget_pos_upper
      C exponent hvExact hvPos
  have hflip :=
    upper_inactive_flip_stays_upper_leaves_lower
      C hunsafe huBase hvBase hc
  refine ⟨c, hc, hflip.1, hflip.2, ?_⟩
  by_cases hblock :
      ∃ w : V,
        w ≠ v ∧
        flipBoolWordAt base c ∈ retainedCompletionWords C w
  · right
    obtain ⟨w, hwv, hw⟩ := hblock
    have hsafe :=
      upper_inactive_flip_blocker_is_safe_to_left
        C huv hunsafe huBase hvBase hc hwv.symm hw
    exact ⟨w, hwv, hw, hsafe.1, hsafe.2.1, hsafe.2.2⟩
  · left
    intro w hw
    by_contra hwv
    exact hblock ⟨w, hwv, hw⟩

/-- Combined unsafe descent: if at least one exact endpoint has positive
exponent, the unsafe overlap has a one-step outlet to a singly-covered word
or a safe residual overlap. -/
theorem unsafe_exact_overlap_nonzero_endpoint_has_safe_descent
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
    (hvExact : ExactProjectedBudget C exponent v)
    (hpos : 1 ≤ exponent u ∨ 1 ≤ exponent v) :
    (
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
            u < w ∧ IsResidual C u w ∧
            c ∉ residualForbidden C u w
        )
    )
    ∨
    (
      ∃ c : Fin n,
        c ∈ retainedInactive C v ∧
        flipBoolWordAt base c ∈ retainedCompletionWords C v ∧
        flipBoolWordAt base c ∉ retainedCompletionWords C u ∧
        (
          (∀ w : V,
            flipBoolWordAt base c ∈ retainedCompletionWords C w →
            w = v)
          ∨
          ∃ w : V,
            w ≠ v ∧
            flipBoolWordAt base c ∈ retainedCompletionWords C w ∧
            w < v ∧ IsResidual C w v ∧
            c ∉ residualForbidden C w v
        )
    ) := by
  rcases hpos with huPos | hvPos
  · left
    exact exists_lower_inactive_flip_single_or_safe_overlap
      C exponent huv hunsafe huBase hvBase huExact huPos
  · right
    exact exists_upper_inactive_flip_single_or_safe_overlap
      C exponent huv hunsafe huBase hvBase hvExact hvPos

#print axioms upper_inactive_mem_lower_incoming_of_unsafe_overlap
#print axioms upper_inactive_flip_stays_upper_leaves_lower
#print axioms upper_inactive_flip_blocker_outgoing
#print axioms upper_inactive_flip_blocker_is_safe_to_left
#print axioms exists_upper_inactive_flip_single_or_safe_overlap
#print axioms unsafe_exact_overlap_nonzero_endpoint_has_safe_descent

end OrderedEdgeColoring
end JSP000404Research
