import JSP000404Research.ResidualLossExtremeInward
import JSP000404Research.ResidualAugmentingState
import Mathlib.Tactic

/-!
# Structural inward transition from an extreme projected-loss word

The blocker-level inward theorem says that after choosing one of two distinct
active exits at a global extreme loss vertex, every carrier of the translated
word lies strictly between the global extremes.

Combining this with the global 0/1/2 completion-state trichotomy gives a
closed structural transition:

* a genuine Boolean hole;
* a unique single carrier strictly in the interior;
* a residual overlap pair whose two carriers are both strictly in the interior.

Thus every nonterminal state after the first extreme-loss displacement has
strictly smaller carrier span.
-/

namespace JSP000404Research
namespace OrderedEdgeColoring

theorem minimum_loss_two_exit_structural_inward
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
    (hbottomLoss : bottom ∈ projectedLossVertices C exponent)
    {word : Fin n → Bool}
    (hword : word ∈ retainedCompletionWords C bottom)
    {c d : Fin n}
    (hc : c ∈ retainedActive C bottom)
    (hd : d ∈ retainedActive C bottom)
    (hcd : c ≠ d) :
    ∃ e : Fin n,
      (e = c ∨ e = d) ∧
      let y := flipBoolWordAt word e
      y ∉ coveredCompletionWords C
      ∨
      (∃ w : V,
        IsSingleCompletionWord C w y ∧
        bottom < w ∧ w < top)
      ∨
      (∃ u v : V,
        u < v ∧
        IsResidual C u v ∧
        y ∈ retainedCompletionWords C u ∧
        y ∈ retainedCompletionWords C v ∧
        bottom < u ∧ u < top ∧
        bottom < v ∧ v < top) := by
  obtain ⟨e,hecd,_heOut,_heOwner,_heTop,hinterior⟩ :=
    minimum_loss_two_exit_avoids_max_and_owner
      C exponent hexp honeLoss
      hmin hmax hbt hbottomLoss hword hc hd hcd
  refine ⟨e,hecd,?_⟩
  dsimp
  rcases completionWord_structural_trichotomy
      C (flipBoolWordAt word e)
    with hhole | hsingle | hoverlap
  · exact Or.inl hhole
  · right
    left
    obtain ⟨w,hwSingle⟩ := hsingle
    have hwInt := hinterior w hwSingle.1
    exact ⟨w,hwSingle,hwInt.1,hwInt.2⟩
  · right
    right
    obtain ⟨u,v,huv,hres,hu,hv⟩ := hoverlap
    have huInt := hinterior u hu
    have hvInt := hinterior v hv
    exact ⟨u,v,huv,hres,hu,hv,
      huInt.1,huInt.2,hvInt.1,hvInt.2⟩

theorem maximum_loss_two_exit_structural_inward
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
    (htopLoss : top ∈ projectedLossVertices C exponent)
    {word : Fin n → Bool}
    (hword : word ∈ retainedCompletionWords C top)
    {c d : Fin n}
    (hc : c ∈ retainedActive C top)
    (hd : d ∈ retainedActive C top)
    (hcd : c ≠ d) :
    ∃ e : Fin n,
      (e = c ∨ e = d) ∧
      let y := flipBoolWordAt word e
      y ∉ coveredCompletionWords C
      ∨
      (∃ w : V,
        IsSingleCompletionWord C w y ∧
        bottom < w ∧ w < top)
      ∨
      (∃ u v : V,
        u < v ∧
        IsResidual C u v ∧
        y ∈ retainedCompletionWords C u ∧
        y ∈ retainedCompletionWords C v ∧
        bottom < u ∧ u < top ∧
        bottom < v ∧ v < top) := by
  obtain ⟨e,hecd,_heIn,_heOwner,_heBottom,hinterior⟩ :=
    maximum_loss_two_exit_avoids_min_and_owner
      C exponent hexp honeLoss
      hmin hmax hbt htopLoss hword hc hd hcd
  refine ⟨e,hecd,?_⟩
  dsimp
  rcases completionWord_structural_trichotomy
      C (flipBoolWordAt word e)
    with hhole | hsingle | hoverlap
  · exact Or.inl hhole
  · right
    left
    obtain ⟨w,hwSingle⟩ := hsingle
    have hwInt := hinterior w hwSingle.1
    exact ⟨w,hwSingle,hwInt.1,hwInt.2⟩
  · right
    right
    obtain ⟨u,v,huv,hres,hu,hv⟩ := hoverlap
    have huInt := hinterior u hu
    have hvInt := hinterior v hv
    exact ⟨u,v,huv,hres,hu,hv,
      huInt.1,huInt.2,hvInt.1,hvInt.2⟩

#print axioms minimum_loss_two_exit_structural_inward
#print axioms maximum_loss_two_exit_structural_inward

end OrderedEdgeColoring
end JSP000404Research
