import JSP000404Research.ResidualSecondLayerTripleCanonical
import JSP000404Research.ResidualEnlargedCandidateBlock
import JSP000404Research.ResidualLossTranslatedConflict
import Mathlib.Tactic

/-!
# Preserve the third source carrier in a Q/T/T state

Suppose a common enlarged-block word comes from three distinct projected-loss
vertices u,v,w.  After canonicalizing u and v as translated owners, the third
original carrier w has only two possibilities.

* If the common word is in Q_w, then the Q-owner is w itself, because exact
  projected-loss completion cubes are disjoint across distinct vertices.
* Otherwise the word lies in an active translated slice T_{w,cz}.  Its
  coordinate cz is different from both translated coordinates cx,cy, since
  equal-coordinate translated slices at two distinct loss vertices are
  disjoint.

Thus the third original source is never lost: it is either the completion
owner or already a valid third translated owner.
-/

namespace JSP000404Research
namespace OrderedEdgeColoring

theorem QTT_third_source_is_Q_owner_or_third_translated
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexp : ∀ q, exponent q ≤ n)
    (honeLoss :
      ∀ q, (active C q).card ≤ n - exponent q + 1)
    {s x y r : V}
    (hsx : s ≠ x)
    (hsy : s ≠ y)
    (hxr : x ≠ r)
    (hyr : y ≠ r)
    (hsLoss : s ∈ projectedLossVertices C exponent)
    (hxLoss : x ∈ projectedLossVertices C exponent)
    (hyLoss : y ∈ projectedLossVertices C exponent)
    (hrLoss : r ∈ projectedLossVertices C exponent)
    {word : Fin n → Bool}
    {cx cy : Fin n}
    (hcxy : cx ≠ cy)
    (hsQ : word ∈ retainedCompletionWords C s)
    (hxT : word ∈ translatedCompletionWords C x cx)
    (hyT : word ∈ translatedCompletionWords C y cy)
    (hrBlock :
      word ∈ enlargedProjectedCandidateBlock C exponent r) :
    r = s ∨
    ∃ cz : Fin n,
      cz ∈ retainedActive C r ∧
      cx ≠ cz ∧ cy ≠ cz ∧
      word ∈ translatedCompletionWords C r cz := by
  classical
  rw [enlargedProjectedCandidateBlock_loss
    C exponent hrLoss] at hrBlock
  unfold allActiveLossCandidateBlock at hrBlock
  rcases Finset.mem_union.mp hrBlock with hrQ | hrT
  · left
    by_contra hrs
    exact Finset.disjoint_left.mp
      (projectedLoss_completion_disjoint
        C exponent hexp honeLoss hsLoss hrs.symm)
      hsQ hrQ
  · right
    unfold allActiveTranslatedWords at hrT
    obtain ⟨cz,hczActive,hczT⟩ :=
      Finset.mem_biUnion.mp hrT
    have hcxz : cx ≠ cz := by
      intro h
      subst cz
      exact Finset.disjoint_left.mp
        (translated_loss_blocks_disjoint_same_coordinate
          C exponent hexp honeLoss
          hxLoss hrLoss hxr cx)
        hxT hczT
    have hcyz : cy ≠ cz := by
      intro h
      subst cz
      exact Finset.disjoint_left.mp
        (translated_loss_blocks_disjoint_same_coordinate
          C exponent hexp honeLoss
          hyLoss hrLoss hyr cy)
        hyT hczT
    exact ⟨cz,hczActive,hcxz,hcyz,hczT⟩

#print axioms QTT_third_source_is_Q_owner_or_third_translated

end OrderedEdgeColoring
end JSP000404Research
