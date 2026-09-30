import JSP000404Research.ResidualLossExtremeInward
import JSP000404Research.ResidualCompletionAccounting
import Mathlib.Tactic

/-!
# Terminal extreme-loss inward step

If bottom and top are global extremes and there is no vertex strictly between
them, the inward two-exit theorem has nowhere left to place a blocker.
Therefore its selected translated word is a genuine Boolean hole.

This is the zero-interior base case for an interval-size induction on the
extreme-loss obstruction.
-/

namespace JSP000404Research
namespace OrderedEdgeColoring

theorem minimum_loss_two_exit_hole_of_no_interior
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexp : ∀ v, exponent v ≤ n)
    (honeLoss :
      ∀ v, (active C v).card ≤ n - exponent v + 1)
    {bottom top : V}
    (hmin : ∀ w : V, bottom ≤ w)
    (hmax : ∀ w : V, w ≤ top)
    (hbt : bottom ≠ top)
    (hnoInterior :
      ¬ ∃ w : V, bottom < w ∧ w < top)
    (hbottomLoss : bottom ∈ projectedLossVertices C exponent)
    {word : Fin n → Bool}
    (hword : word ∈ retainedCompletionWords C bottom)
    {c d : Fin n}
    (hc : c ∈ retainedActive C bottom)
    (hd : d ∈ retainedActive C bottom)
    (hcd : c ≠ d) :
    ∃ e : Fin n,
      (e = c ∨ e = d) ∧
      flipBoolWordAt word e ∉ coveredCompletionWords C := by
  obtain ⟨e,hecd,_heOut,_heOwner,_heTop,hinterior⟩ :=
    minimum_loss_two_exit_avoids_max_and_owner
      C exponent hexp honeLoss
      hmin hmax hbt hbottomLoss hword hc hd hcd
  refine ⟨e,hecd,?_⟩
  intro hcovered
  have hnonempty :
      (completionFibre C (flipBoolWordAt word e)).Nonempty :=
    (mem_coveredCompletionWords C
      (flipBoolWordAt word e)).1 hcovered
  obtain ⟨w,hwF⟩ := hnonempty
  have hw :
      flipBoolWordAt word e ∈ retainedCompletionWords C w :=
    (mem_completionFibre C _ w).1 hwF
  exact hnoInterior ⟨w,(hinterior w hw).1,(hinterior w hw).2⟩

theorem maximum_loss_two_exit_hole_of_no_interior
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexp : ∀ v, exponent v ≤ n)
    (honeLoss :
      ∀ v, (active C v).card ≤ n - exponent v + 1)
    {bottom top : V}
    (hmin : ∀ w : V, bottom ≤ w)
    (hmax : ∀ w : V, w ≤ top)
    (hbt : bottom ≠ top)
    (hnoInterior :
      ¬ ∃ w : V, bottom < w ∧ w < top)
    (htopLoss : top ∈ projectedLossVertices C exponent)
    {word : Fin n → Bool}
    (hword : word ∈ retainedCompletionWords C top)
    {c d : Fin n}
    (hc : c ∈ retainedActive C top)
    (hd : d ∈ retainedActive C top)
    (hcd : c ≠ d) :
    ∃ e : Fin n,
      (e = c ∨ e = d) ∧
      flipBoolWordAt word e ∉ coveredCompletionWords C := by
  obtain ⟨e,hecd,_heIn,_heOwner,_heBottom,hinterior⟩ :=
    maximum_loss_two_exit_avoids_min_and_owner
      C exponent hexp honeLoss
      hmin hmax hbt htopLoss hword hc hd hcd
  refine ⟨e,hecd,?_⟩
  intro hcovered
  have hnonempty :
      (completionFibre C (flipBoolWordAt word e)).Nonempty :=
    (mem_coveredCompletionWords C
      (flipBoolWordAt word e)).1 hcovered
  obtain ⟨w,hwF⟩ := hnonempty
  have hw :
      flipBoolWordAt word e ∈ retainedCompletionWords C w :=
    (mem_completionFibre C _ w).1 hwF
  exact hnoInterior ⟨w,(hinterior w hw).1,(hinterior w hw).2⟩

#print axioms minimum_loss_two_exit_hole_of_no_interior
#print axioms maximum_loss_two_exit_hole_of_no_interior

end OrderedEdgeColoring
end JSP000404Research
