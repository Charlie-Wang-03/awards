import JSP000404Research.ResidualOverlapFlip
import JSP000404Research.ResidualUniqueBlocker
import Mathlib.Tactic

/-!
# Deterministic blocker transition for safe active-only flips

For a safe residual overlap u<v, suppose the chosen safe coordinate is active
at exactly one endpoint. Flipping that coordinate preserves membership in the
other endpoint cube and leaves the active endpoint cube.

Because one old endpoint remains as an anchor and completion multiplicity is
at most two, there is at most one additional blocker. Moreover that blocker
must activate the flipped coordinate with the opposite canonical bit.

This gives a deterministic next residual carrier. If the blocker lies beyond
the anchor in the outward direction, the same flipped coordinate is already a
safe target for the next carrier.
-/

namespace JSP000404Research
namespace OrderedEdgeColoring

theorem safe_left_active_flip_blocker_incoming
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    {u v w : V} {word : Fin n → Bool} {c : Fin n}
    (huv : u < v)
    (hu : word ∈ retainedCompletionWords C u)
    (hv : word ∈ retainedCompletionWords C v)
    (hsafe : c ∉ residualForbidden C u v)
    (hcu : c ∈ retainedActive C u)
    (hw :
      flipRetainedWord word c ∈ retainedCompletionWords C w)
    (hwv : w ≠ v) :
    c ∈ incomingRetained C w := by
  have hflip :=
    flip_overlap_to_right_single C hu hv hsafe hcu
  have hcv : c ∉ retainedActive C v := by
    intro h
    exact safe_overlap_not_active_both C hu hv hsafe ⟨hcu,h⟩
  have hwu : w ≠ u := by
    intro h
    subst w
    exact hflip.2 hw
  have hcW : c ∈ retainedActive C w := by
    by_contra hcInactive
    have hwOrig :
        word ∈ retainedCompletionWords C w := by
      apply (mem_retainedCompletionWords C w word).2
      intro d hd
      have hdc : d ≠ c := by
        intro h
        subst d
        exact hcInactive hd
      have hcomp :=
        (mem_retainedCompletionWords C w
          (flipRetainedWord word c)).1 hw
      rw [flipRetainedWord_off word hdc] at hcomp
      exact hcomp d hd
    exact no_three_distinct_share_retained_completion
      C (ne_of_lt huv) hwu.symm hwv.symm hu hv hwOrig
  have hcNotInU : c ∉ incomingRetained C u := by
    intro hc
    exact hsafe (Finset.mem_union_left _ hc)
  have hcOutU : c ∈ outgoingRetained C u := by
    rw [retainedActive_eq_incoming_union_outgoing C u] at hcu
    rcases Finset.mem_union.mp hcu with hin | hout
    · exact False.elim (hcNotInU hin)
    · exact hout
  have hbitU :
      retainedBit C u c = false :=
    retainedBit_false_of_outgoingRetained C hcOutU
  have hwordC :
      word c = false := by
    exact ((mem_retainedCompletionWords C u word).1 hu c hcu).trans hbitU
  have hwComp :=
    (mem_retainedCompletionWords C w
      (flipRetainedWord word c)).1 hw
  have hwAt := hwComp c hcW
  have hflipC : flipRetainedWord word c c = true := by
    simp [flipRetainedWord, hwordC]
  rw [hflipC] at hwAt
  have hbitW : retainedBit C w c = true := hwAt.symm
  exact (mem_incomingRetained_iff_retainedBit_true C w c).2 hbitW

theorem safe_left_active_flip_blocker_outward_safe
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    {u v w : V} {word : Fin n → Bool} {c : Fin n}
    (huv : u < v)
    (hu : word ∈ retainedCompletionWords C u)
    (hv : word ∈ retainedCompletionWords C v)
    (hsafe : c ∉ residualForbidden C u v)
    (hcu : c ∈ retainedActive C u)
    (hw :
      flipRetainedWord word c ∈ retainedCompletionWords C w)
    (hvw : v < w) :
    IsResidual C v w ∧
      c ∉ residualForbidden C v w := by
  have hflip :=
    flip_overlap_to_right_single C hu hv hsafe hcu
  have hres :=
    isResidual_of_retainedCompletion_overlap_lt
      C hvw hflip.1 hw
  have hcv : c ∉ retainedActive C v := by
    intro h
    exact safe_overlap_not_active_both C hu hv hsafe ⟨hcu,h⟩
  have hcInW :=
    safe_left_active_flip_blocker_incoming
      C huv hu hv hsafe hcu hw (ne_of_gt hvw)
  have hcNotInV : c ∉ incomingRetained C v := by
    intro h
    exact hcv (incomingRetained_subset_retainedActive C v h)
  have hcNotOutW : c ∉ outgoingRetained C w := by
    intro h
    exact Finset.disjoint_left.mp
      (incomingRetained_disjoint_outgoingRetained C w)
      hcInW h
  refine ⟨hres, ?_⟩
  unfold residualForbidden
  rw [Finset.mem_union]
  push_neg
  exact ⟨hcNotInV, hcNotOutW⟩

theorem safe_left_active_flip_single_or_unique_blocker
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    {u v : V} {word : Fin n → Bool} {c : Fin n}
    (huv : u < v)
    (hu : word ∈ retainedCompletionWords C u)
    (hv : word ∈ retainedCompletionWords C v)
    (hsafe : c ∉ residualForbidden C u v)
    (hcu : c ∈ retainedActive C u) :
    let y := flipRetainedWord word c
    (∀ z : V, y ∈ retainedCompletionWords C z → z = v)
    ∨
    ∃ w : V,
      w ≠ v ∧
      y ∈ retainedCompletionWords C w ∧
      (if hvw : v < w then
        IsResidual C v w ∧
          c ∉ residualForbidden C v w
       else
        w < v ∧ IsResidual C w v) ∧
      ∀ z : V,
        z ≠ v →
        y ∈ retainedCompletionWords C z →
        z = w := by
  dsimp
  have hflip :=
    flip_overlap_to_right_single C hu hv hsafe hcu
  rcases single_or_unique_additional_blocker C hflip.1 with hsingle | hblock
  · exact Or.inl hsingle
  · right
    obtain ⟨w, hwv, hw, huniq⟩ := hblock
    refine ⟨w, hwv, hw, ?_, huniq⟩
    by_cases hvw : v < w
    · simp only [hvw, dif_pos]
      exact safe_left_active_flip_blocker_outward_safe
        C huv hu hv hsafe hcu hw hvw
    · have hwvlt : w < v := lt_of_le_of_ne
        (le_of_not_gt hvw) hwv
      simp only [hvw, dif_neg]
      exact ⟨hwvlt,
        isResidual_of_retainedCompletion_overlap_lt
          C hwvlt hw hflip.1⟩


theorem safe_right_active_flip_blocker_outgoing
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    {u v w : V} {word : Fin n → Bool} {c : Fin n}
    (huv : u < v)
    (hu : word ∈ retainedCompletionWords C u)
    (hv : word ∈ retainedCompletionWords C v)
    (hsafe : c ∉ residualForbidden C u v)
    (hcv : c ∈ retainedActive C v)
    (hw :
      flipRetainedWord word c ∈ retainedCompletionWords C w)
    (hwu : w ≠ u) :
    c ∈ outgoingRetained C w := by
  have hflip :=
    flip_overlap_to_left_single C hu hv hsafe hcv
  have hcu : c ∉ retainedActive C u := by
    intro h
    exact safe_overlap_not_active_both C hu hv hsafe ⟨h,hcv⟩
  have hwv : w ≠ v := by
    intro h
    subst w
    exact hflip.2 hw
  have hcW : c ∈ retainedActive C w := by
    by_contra hcInactive
    have hwOrig :
        word ∈ retainedCompletionWords C w := by
      apply (mem_retainedCompletionWords C w word).2
      intro d hd
      have hdc : d ≠ c := by
        intro h
        subst d
        exact hcInactive hd
      have hcomp :=
        (mem_retainedCompletionWords C w
          (flipRetainedWord word c)).1 hw
      rw [flipRetainedWord_off word hdc] at hcomp
      exact hcomp d hd
    exact no_three_distinct_share_retained_completion
      C (ne_of_lt huv) hwu.symm hwv.symm hu hv hwOrig
  have hcNotOutV : c ∉ outgoingRetained C v := by
    intro hc
    exact hsafe (Finset.mem_union_right _ hc)
  have hcInV : c ∈ incomingRetained C v := by
    rw [retainedActive_eq_incoming_union_outgoing C v] at hcv
    rcases Finset.mem_union.mp hcv with hin | hout
    · exact hin
    · exact False.elim (hcNotOutV hout)
  have hbitV :
      retainedBit C v c = true :=
    (mem_incomingRetained_iff_retainedBit_true C v c).1 hcInV
  have hwordC :
      word c = true := by
    exact ((mem_retainedCompletionWords C v word).1 hv c hcv).trans hbitV
  have hwComp :=
    (mem_retainedCompletionWords C w
      (flipRetainedWord word c)).1 hw
  have hwAt := hwComp c hcW
  have hflipC : flipRetainedWord word c c = false := by
    simp [flipRetainedWord, hwordC]
  rw [hflipC] at hwAt
  have hbitW : retainedBit C w c = false := hwAt.symm
  rw [retainedActive_eq_incoming_union_outgoing C w] at hcW
  rcases Finset.mem_union.mp hcW with hin | hout
  · have htrue :=
      (mem_incomingRetained_iff_retainedBit_true C w c).1 hin
    rw [hbitW] at htrue
    contradiction
  · exact hout

theorem safe_right_active_flip_blocker_outward_safe
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    {u v w : V} {word : Fin n → Bool} {c : Fin n}
    (huv : u < v)
    (hu : word ∈ retainedCompletionWords C u)
    (hv : word ∈ retainedCompletionWords C v)
    (hsafe : c ∉ residualForbidden C u v)
    (hcv : c ∈ retainedActive C v)
    (hw :
      flipRetainedWord word c ∈ retainedCompletionWords C w)
    (hwu : w < u) :
    IsResidual C w u ∧
      c ∉ residualForbidden C w u := by
  have hflip :=
    flip_overlap_to_left_single C hu hv hsafe hcv
  have hres :=
    isResidual_of_retainedCompletion_overlap_lt
      C hwu hw hflip.1
  have hcu : c ∉ retainedActive C u := by
    intro h
    exact safe_overlap_not_active_both C hu hv hsafe ⟨h,hcv⟩
  have hcOutW :=
    safe_right_active_flip_blocker_outgoing
      C huv hu hv hsafe hcv hw (ne_of_lt hwu)
  have hcNotInW : c ∉ incomingRetained C w := by
    intro h
    exact Finset.disjoint_left.mp
      (incomingRetained_disjoint_outgoingRetained C w)
      h hcOutW
  have hcNotOutU : c ∉ outgoingRetained C u := by
    intro h
    exact hcu (outgoingRetained_subset_retainedActive C u h)
  refine ⟨hres, ?_⟩
  unfold residualForbidden
  rw [Finset.mem_union]
  push_neg
  exact ⟨hcNotInW, hcNotOutU⟩

theorem safe_right_active_flip_single_or_unique_blocker
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    {u v : V} {word : Fin n → Bool} {c : Fin n}
    (huv : u < v)
    (hu : word ∈ retainedCompletionWords C u)
    (hv : word ∈ retainedCompletionWords C v)
    (hsafe : c ∉ residualForbidden C u v)
    (hcv : c ∈ retainedActive C v) :
    let y := flipRetainedWord word c
    (∀ z : V, y ∈ retainedCompletionWords C z → z = u)
    ∨
    ∃ w : V,
      w ≠ u ∧
      y ∈ retainedCompletionWords C w ∧
      (if hwu : w < u then
        IsResidual C w u ∧
          c ∉ residualForbidden C w u
       else
        u < w ∧ IsResidual C u w) ∧
      ∀ z : V,
        z ≠ u →
        y ∈ retainedCompletionWords C z →
        z = w := by
  dsimp
  have hflip :=
    flip_overlap_to_left_single C hu hv hsafe hcv
  rcases single_or_unique_additional_blocker C hflip.1 with hsingle | hblock
  · exact Or.inl hsingle
  · right
    obtain ⟨w, hwu, hw, huniq⟩ := hblock
    refine ⟨w, hwu, hw, ?_, huniq⟩
    by_cases hwuLt : w < u
    · simp only [hwuLt, dif_pos]
      exact safe_right_active_flip_blocker_outward_safe
        C huv hu hv hsafe hcv hw hwuLt
    · have huw : u < w := lt_of_le_of_ne
        (le_of_not_gt hwuLt) hwu.symm
      simp only [hwuLt, dif_neg]
      exact ⟨huw,
        isResidual_of_retainedCompletion_overlap_lt
          C huw hflip.1 hw⟩

#print axioms safe_left_active_flip_blocker_incoming
#print axioms safe_left_active_flip_blocker_outward_safe
#print axioms safe_left_active_flip_single_or_unique_blocker
#print axioms safe_right_active_flip_blocker_outgoing
#print axioms safe_right_active_flip_blocker_outward_safe
#print axioms safe_right_active_flip_single_or_unique_blocker

end OrderedEdgeColoring
end JSP000404Research
