import JSP000404Research.ResidualThreeCoordinateAntipode
import JSP000404Research.ResidualQTTTRepeatedPalette
import JSP000404Research.ResidualCompletionFibreLabel
import Mathlib.Tactic

/-!
# Arbitrary-n Q/T/T/T three-coordinate antipode terminal

For a saturated second-layer Q/T/T/T state, assume one retained colour is
active at all four vertices.  The repeated-palette theorem gives at least one
translated owner whose three-coordinate palette equals that of the completion
owner s.

Consider the word obtained from the common Q/T/T/T word by flipping all three
owner coordinates.  It is outside s's enlarged block, and outside the enlarged
block of every translated owner whose palette equals s.

Hence either this three-coordinate antipode is a genuine Boolean completion
hole, or any completion blocker is different from s and from at least one
equal-palette translated owner.
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
        QTT_equal_palette_partner_excludes_triple_antipode
          C exponent hxLoss hcxy hcxz hcyz
          hsActive hxEq hcxX hxT
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
        QTT_equal_palette_partner_excludes_triple_antipode
          C exponent hyLoss
          hcyz hcyz.symm hcxy
          (by
            simpa [Finset.pair_comm, Finset.insert_comm,
              Finset.insert_left_comm] using hsActive)
          hyEq hcyY hyT
      -- The helper above is parameterized with the translated coordinate
      -- first.  Reordering the three flips does not change the antipode;
      -- use the direct three-active exclusion instead to avoid permutation
      -- bookkeeping.
      have hcxY : cx ∈ retainedActive C y := by
        rw [hyEq,hsActive]
        simp
      have hczY : cz ∈ retainedActive C y := by
        rw [hyEq,hsActive]
        simp
      have hyBase :
          flipBoolWordAt word cy ∈ retainedCompletionWords C y :=
        (mem_translatedCompletionWords C y cy word).1 hyT
      have hyAntiOut :
          anti ∉ enlargedProjectedCandidateBlock C exponent y := by
        -- anti differs from hyBase at cx and cz; a one-coordinate translate
        -- cannot repair both active discrepancies.
        dsimp [anti]
        rw [enlargedProjectedCandidateBlock_loss C exponent hyLoss]
        unfold allActiveLossCandidateBlock
        intro hm
        rcases Finset.mem_union.mp hm with hQ | hT
        · have hcomp :=
            (mem_retainedCompletionWords C y
              (tripleFlipBoolWordN word cx cy cz)).1 hQ
          have hbase :=
            (mem_retainedCompletionWords C y
              (flipBoolWordAt word cy)).1 hyBase
          have h1 := hbase cx hcxY
          have h2 := hcomp cx hcxY
          rw [flipBoolWordAt_off word hcxy.symm,
              tripleFlipBoolWordN_at_a word hcxy hcxz, h1] at h2
          cases h : retainedBit C y cx <;> simp [h] at h2
        · unfold allActiveTranslatedWords at hT
          obtain ⟨e,he,hTe⟩ := Finset.mem_biUnion.mp hT
          have hantiBase :
              flipBoolWordAt
                (tripleFlipBoolWordN word cx cy cz) e
                ∈ retainedCompletionWords C y :=
            (mem_translatedCompletionWords C y e _).1 hTe
          have hcomp :=
            (mem_retainedCompletionWords C y _).1 hantiBase
          by_cases hecx : e = cx
          · subst e
            have h1 :=
              (mem_retainedCompletionWords C y
                (flipBoolWordAt word cy)).1 hyBase cz hczY
            have h2 := hcomp cz hczY
            rw [flipBoolWordAt_off _ hcxz.symm,
                tripleFlipBoolWordN_at_c word hcxz hcyz] at h2
            rw [flipBoolWordAt_off word hcyz] at h1
            rw [h1] at h2
            cases h : retainedBit C y cz <;> simp [h] at h2
          · have h1 :=
              (mem_retainedCompletionWords C y
                (flipBoolWordAt word cy)).1 hyBase cx hcxY
            have h2 := hcomp cx hcxY
            rw [flipBoolWordAt_off _ hecx,
                tripleFlipBoolWordN_at_a word hcxy hcxz] at h2
            rw [flipBoolWordAt_off word hcxy.symm] at h1
            rw [h1] at h2
            cases h : retainedBit C y cx <;> simp [h] at h2
      exact hyAntiOut
        (by
          rw [enlargedProjectedCandidateBlock_loss C exponent hyLoss]
          unfold allActiveLossCandidateBlock
          exact Finset.mem_union_left _ hrQ)
    · right; right
      refine ⟨hzEq,?_⟩
      intro hrz
      subst r
      have hcxZ : cx ∈ retainedActive C z := by
        rw [hzEq,hsActive]
        simp
      have hcyZ : cy ∈ retainedActive C z := by
        rw [hzEq,hsActive]
        simp
      have hzBase :
          flipBoolWordAt word cz ∈ retainedCompletionWords C z :=
        (mem_translatedCompletionWords C z cz word).1 hzT
      have hzAntiOut :
          anti ∉ enlargedProjectedCandidateBlock C exponent z := by
        dsimp [anti]
        rw [enlargedProjectedCandidateBlock_loss C exponent hzLoss]
        unfold allActiveLossCandidateBlock
        intro hm
        rcases Finset.mem_union.mp hm with hQ | hT
        · have hcomp :=
            (mem_retainedCompletionWords C z
              (tripleFlipBoolWordN word cx cy cz)).1 hQ
          have hbase :=
            (mem_retainedCompletionWords C z
              (flipBoolWordAt word cz)).1 hzBase
          have h1 := hbase cx hcxZ
          have h2 := hcomp cx hcxZ
          rw [flipBoolWordAt_off word hcxz.symm,
              tripleFlipBoolWordN_at_a word hcxy hcxz, h1] at h2
          cases h : retainedBit C z cx <;> simp [h] at h2
        · unfold allActiveTranslatedWords at hT
          obtain ⟨e,he,hTe⟩ := Finset.mem_biUnion.mp hT
          have hantiBase :
              flipBoolWordAt
                (tripleFlipBoolWordN word cx cy cz) e
                ∈ retainedCompletionWords C z :=
            (mem_translatedCompletionWords C z e _).1 hTe
          have hcomp :=
            (mem_retainedCompletionWords C z _).1 hantiBase
          by_cases hecx : e = cx
          · subst e
            have h1 :=
              (mem_retainedCompletionWords C z
                (flipBoolWordAt word cz)).1 hzBase cy hcyZ
            have h2 := hcomp cy hcyZ
            rw [flipBoolWordAt_off _ hcxy.symm,
                tripleFlipBoolWordN_at_b word hcxy hcyz] at h2
            rw [flipBoolWordAt_off word hcyz.symm] at h1
            rw [h1] at h2
            cases h : retainedBit C z cy <;> simp [h] at h2
          · have h1 :=
              (mem_retainedCompletionWords C z
                (flipBoolWordAt word cz)).1 hzBase cx hcxZ
            have h2 := hcomp cx hcxZ
            rw [flipBoolWordAt_off _ hecx,
                tripleFlipBoolWordN_at_a word hcxy hcxz] at h2
            rw [flipBoolWordAt_off word hcxz.symm] at h1
            rw [h1] at h2
            cases h : retainedBit C z cx <;> simp [h] at h2
      exact hzAntiOut
        (by
          rw [enlargedProjectedCandidateBlock_loss C exponent hzLoss]
          unfold allActiveLossCandidateBlock
          exact Finset.mem_union_left _ hrQ)

#print axioms QTTT_common_colour_tripleAntipode_hole_or_blocker_avoids_equal_partner

end OrderedEdgeColoring
end JSP000404Research
