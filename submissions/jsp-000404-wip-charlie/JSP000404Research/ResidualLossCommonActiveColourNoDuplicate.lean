import JSP000404Research.ResidualLossDuplicateDebtLedger
import Mathlib.Tactic

/-!
# Actual common retained-active coordinate eliminates ENTIRE duplicate debt

The projected-loss duplicate term is NOT inevitable. If all true
projected-loss vertices can choose one genuinely retained-active colour
c0, choose that SAME colour at every such vertex. Then ALL translated
loss words belong to just one coordinate slice; different coordinate
slices are disjoint and the exact duplicate debt is LITERALLY ZERO.

This is a POSITIVE source-native elimination of an entire separate
term in the one remaining global payment frontier, under a checkable
original colouring palette-intersection condition. In particular it
does not use any alleged hole/surplus credit. The condition is
not claimed to hold for all planar AngleCap configurations.
-/

namespace JSP000404Research
namespace OrderedEdgeColoring

/-- If each actually projected-loss source uses ONE fixed chosen
retained coordinate, any nonempty translated-loss slice must carry
that coordinate. Thus the exact cross-coordinate overcount vanishes. -/
theorem translated_loss_duplicate_zero_of_common_chosen_coordinate
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (choice : V → Fin n) (c0 : Fin n)
    (hconstant :
      ∀ v ∈ projectedLossVertices C exponent, choice v = c0) :
    translatedLossDuplicateDebt C exponent choice = 0 := by
  classical
  have hdisjoint :
      (((Finset.univ : Finset (Fin n)) : Set (Fin n))).PairwiseDisjoint
        (fun c => translatedLossSliceWords C exponent choice c) := by
    intro c hc d hd hcd
    change Disjoint
      (translatedLossSliceWords C exponent choice c)
      (translatedLossSliceWords C exponent choice d)
    rw [Finset.disjoint_left]
    intro word hwc hwd
    obtain ⟨v,hv,_⟩ := Finset.mem_biUnion.mp hwc
    obtain ⟨u,hu,_⟩ := Finset.mem_biUnion.mp hwd
    have hvdata := (mem_lossCoordinateSlice
      C exponent choice c v).1 hv
    have hudata := (mem_lossCoordinateSlice
      C exponent choice d u).1 hu
    have hceq : c = c0 := hvdata.2.symm.trans
      (hconstant v hvdata.1)
    have hdeq : d = c0 := hudata.2.symm.trans
      (hconstant u hudata.1)
    exact hcd (hceq.trans hdeq.symm)
  unfold translatedLossDuplicateDebt translatedLossAllCoordinateWords
  rw [Finset.card_biUnion hdisjoint]
  simp

/-- A NONEMPTY common retained-active palette intersection across the
ACTUAL projected-loss sources gives an explicit active choice function
with ZERO exact duplicate loss debt. No forward/reverse hard-source
or covered blocker debt is omitted by this statement. -/
theorem common_retained_active_colour_gives_zero_loss_duplicate_choice
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (c0 : Fin n)
    (hcommon :
      ∀ v ∈ projectedLossVertices C exponent,
        c0 ∈ retainedActive C v) :
    ∃ choice : V → Fin n,
      (∀ v ∈ projectedLossVertices C exponent,
        choice v ∈ retainedActive C v) ∧
      translatedLossDuplicateDebt C exponent choice = 0 := by
  refine ⟨fun _ => c0, ?_, ?_⟩
  · intro v hv
    exact hcommon v hv
  · exact translated_loss_duplicate_zero_of_common_chosen_coordinate
      C exponent (fun _ => c0) c0 (by intros; rfl)

#print axioms translated_loss_duplicate_zero_of_common_chosen_coordinate
#print axioms common_retained_active_colour_gives_zero_loss_duplicate_choice

end OrderedEdgeColoring
end JSP000404Research
