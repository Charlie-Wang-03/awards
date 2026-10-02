import JSP000404Research.ResidualThreeCoordinateAntipode
import JSP000404Research.ResidualQTTTRepeatedPalette
import JSP000404Research.ResidualCompletionFibreLabel
import Mathlib.Tactic

/-!
# Arbitrary-n Q/T/T/T three-coordinate antipode terminal

A common retained colour in the saturated Q/T/T/T state forces at least one
translated owner to have exactly the same three-coordinate retained palette as
the completion owner s.

The triple owner-coordinate flip of the common word is outside s's enlarged
block and outside every such equal-palette partner block.  Therefore it is
either a genuine Boolean completion hole, or every completion blocker avoids s
and at least one equal-palette translated owner.
-/

namespace JSP000404Research
namespace OrderedEdgeColoring

theorem QTTT_common_colour_tripleAntipode_hole_or_blocker_avoids_equal_partner
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexp : ∀ q, exponent q ≤ n)
    (honeLoss :
      ∀ q, (active C q).card ≤ n - exponent q + 1)
    {s x y z : V}
    (hsx : s ≠ x) (hsy : s ≠ y) (hsz : s ≠ z)
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (hsLoss : s ∈ projectedLossVertices C exponent)
    (hxLoss : x ∈ projectedLossVertices C exponent)
    (hyLoss : y ∈ projectedLossVertices C exponent)
    (hzLoss : z ∈ projectedLossVertices C exponent)
    (hsSecond : exponent s = n - 2)
    (hxSecond : exponent x = n - 2)
    (hySecond : exponent y = n - 2)
    (hzSecond : exponent z = n - 2)
    {word : Fin n → Bool}
    {cx cy cz d : Fin n}
    (hcxy : cx ≠ cy) (hcxz : cx ≠ cz) (hcyz : cy ≠ cz)
    (hsActive : retainedActive C s = {cx,cy,cz})
    (hcommonS : d ∈ retainedActive C s)
    (hcommonX : d ∈ retainedActive C x)
    (hcommonY : d ∈ retainedActive C y)
    (hcommonZ : d ∈ retainedActive C z)
    (hcxX : cx ∈ retainedActive C x)
    (hcyY : cy ∈ retainedActive C y)
    (hczZ : cz ∈ retainedActive C z)
    (hsQ : word ∈ retainedCompletionWords C s)
    (hxT : word ∈ translatedCompletionWords C x cx)
    (hyT : word ∈ translatedCompletionWords C y cy)
    (hzT : word ∈ translatedCompletionWords C z cz) :
    let anti := tripleFlipBoolWordN word cx cy cz
    anti ∉ coveredCompletionWords C
    ∨
    ∃ r : V,
      anti ∈ retainedCompletionWords C r ∧
      r ≠ s ∧
      (
        (retainedActive C x = retainedActive C s ∧ r ≠ x) ∨
        (retainedActive C y = retainedActive C s ∧ r ≠ y) ∨
        (retainedActive C z = retainedActive C s ∧ r ≠ z)
      ) := by
  dsimp
  let anti := tripleFlipBoolWordN word cx cy cz

  have hsOut :
      anti ∉ enlargedProjectedCandidateBlock C exponent s := by
    dsimp [anti]
    exact tripleFlipBoolWordN_outside_enlarged_of_exact_three_palette
      C exponent hsLoss hcxy hcxz hcyz hsActive hsQ

  have hpartner :=
    QTTT_common_colour_forces_some_translated_palette_eq_s
      C exponent hexp honeLoss
      hxy hxz hyz
      hsLoss hxLoss hyLoss hzLoss
      hsSecond hxSecond hySecond hzSecond
      hcxy hcxz hcyz hsActive
      hcommonS hcommonX hcommonY hcommonZ
      hcxX hcyY hczZ
      hxT hyT hzT

  by_cases hhole : anti ∉ coveredCompletionWords C
  · exact Or.inl hhole
  · right
    have hcovered : anti ∈ coveredCompletionWords C := by
      simpa using hhole
    obtain ⟨r,hrF⟩ :=
      (mem_coveredCompletionWords C anti).1 hcovered
    have hrQ :
        anti ∈ retainedCompletionWords C r :=
      (mem_completionFibre C anti r).1 hrF
    have hrs : r ≠ s := by
      intro hrs
      subst r
      apply hsOut
      rw [enlargedProjectedCandidateBlock_loss C exponent hsLoss]
      unfold allActiveLossCandidateBlock
      exact Finset.mem_union_left _ hrQ

    refine ⟨r,hrQ,hrs,?_⟩
    rcases hpartner with hxEq | hyEq | hzEq
    · left
      refine ⟨hxEq,?_⟩
      intro hrx
      subst r
      have hxOut :=
        QTT_equal_palette_x_excludes_triple_antipode
          C exponent hxLoss hcxy hcxz hcyz hsActive hxEq hxT
      exact hxOut
        (by
          rw [enlargedProjectedCandidateBlock_loss C exponent hxLoss]
          unfold allActiveLossCandidateBlock
          exact Finset.mem_union_left _ hrQ)
    · right; left
      refine ⟨hyEq,?_⟩
      intro hry
      subst r
      have hyOut :=
        QTT_equal_palette_y_excludes_triple_antipode
          C exponent hyLoss hcxy hcxz hcyz hsActive hyEq hyT
      exact hyOut
        (by
          rw [enlargedProjectedCandidateBlock_loss C exponent hyLoss]
          unfold allActiveLossCandidateBlock
          exact Finset.mem_union_left _ hrQ)
    · right; right
      refine ⟨hzEq,?_⟩
      intro hrz
      subst r
      have hzOut :=
        QTT_equal_palette_z_excludes_triple_antipode
          C exponent hzLoss hcxy hcxz hcyz hsActive hzEq hzT
      exact hzOut
        (by
          rw [enlargedProjectedCandidateBlock_loss C exponent hzLoss]
          unfold allActiveLossCandidateBlock
          exact Finset.mem_union_left _ hrQ)

#print axioms QTTT_common_colour_tripleAntipode_hole_or_blocker_avoids_equal_partner

end OrderedEdgeColoring
end JSP000404Research
