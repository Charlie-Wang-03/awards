import JSP000404Research.ResidualEnlargedCandidateHall
import JSP000404Research.ResidualLossAllActiveIntersection
import Mathlib.Tactic

/-!
# Collision-neighbour consequence of enlarged loss-block slack

Inside a minimal deficient family for the enlarged candidate blocks, every
projected-loss vertex v has at least |Q_v|+1 shared words.

If all shared words of v came from one other vertex w and w were non-loss,
then B(w)=Q_w.  But the enlarged loss block of v meets any external completion
cube Q_w in at most |Q_v| words, contradiction.

Therefore a loss vertex with a unique collision neighbour can only be paired
with another projected-loss vertex.
-/

namespace JSP000404Research
namespace OrderedEdgeColoring

def EnlargedBlocksCross
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (u v : V) : Prop :=
  (enlargedProjectedCandidateBlock C exponent u ∩
    enlargedProjectedCandidateBlock C exponent v).Nonempty

theorem sharedBlockWords_subset_single_neighbor_intersection
    {V W : Type*} [Fintype V]
    [DecidableEq V] [DecidableEq W]
    (blocks : V → Finset W)
    {T : Finset V} {v w : V}
    (hvT : v ∈ T)
    (hunique :
      ∀ z : V,
        z ∈ T →
        z ≠ v →
        BlocksCross blocks v z →
        z = w) :
    sharedBlockWords blocks T v ⊆
      blocks v ∩ blocks w := by
  intro word hshared
  have hdata :=
    sharedBlockWords_has_other_block blocks hshared
  obtain ⟨hvWord,z,hzT,hzv,hzWord⟩ := hdata
  have hcross : BlocksCross blocks v z := by
    exact ⟨word,hvWord,hzWord⟩
  have hzw := hunique z hzT hzv hcross
  subst z
  exact Finset.mem_inter.mpr ⟨hvWord,hzWord⟩

theorem minimal_enlargedCandidate_loss_unique_neighbor_is_loss
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexp : ∀ x, exponent x ≤ n)
    (honeLoss :
      ∀ x, (active C x).card ≤ n - exponent x + 1)
    {T : Finset V}
    (hdef :
      BlockDeficient
        (fun x => 2 ^ exponent x)
        (enlargedProjectedCandidateBlock C exponent)
        T)
    (hmin :
      ∀ U : Finset V,
        U ⊂ T →
        ¬ BlockDeficient
          (fun x => 2 ^ exponent x)
          (enlargedProjectedCandidateBlock C exponent)
          U)
    {v w : V}
    (hvT : v ∈ T)
    (hvLoss : v ∈ projectedLossVertices C exponent)
    (hvLt : exponent v < n)
    (hunique :
      ∀ z : V,
        z ∈ T →
        z ≠ v →
        EnlargedBlocksCross C exponent v z →
        z = w) :
    w ∈ projectedLossVertices C exponent := by
  classical
  by_contra hwLoss
  have hwBlock :
      enlargedProjectedCandidateBlock C exponent w =
        retainedCompletionWords C w :=
    enlargedProjectedCandidateBlock_nonloss
      C exponent hwLoss
  have hsharedSub :
      sharedBlockWords
          (enlargedProjectedCandidateBlock C exponent)
          T v
        ⊆
      enlargedProjectedCandidateBlock C exponent v ∩
        enlargedProjectedCandidateBlock C exponent w := by
    exact sharedBlockWords_subset_single_neighbor_intersection
      (enlargedProjectedCandidateBlock C exponent)
      hvT
      (by
        intro z hzT hzv hcross
        exact hunique z hzT hzv hcross)
  have hcardShared :
      (sharedBlockWords
        (enlargedProjectedCandidateBlock C exponent)
        T v).card
        ≤
      (enlargedProjectedCandidateBlock C exponent v ∩
        enlargedProjectedCandidateBlock C exponent w).card :=
    Finset.card_le_card hsharedSub
  rw [enlargedProjectedCandidateBlock_loss
        C exponent hvLoss,
      hwBlock] at hcardShared
  have hinter :=
    allActiveLossCandidateBlock_inter_blocker_card_le_cube
      C exponent hexp honeLoss hvLoss
      (by
        intro hvw
        subst w
        exact hwLoss hvLoss)
  have hrequired :=
    minimal_enlargedCandidate_loss_shared_card_ge_cube_add_one
      C exponent hdef hmin hvT hvLoss hvLt
  omega

#print axioms minimal_enlargedCandidate_loss_unique_neighbor_is_loss

end OrderedEdgeColoring
end JSP000404Research
