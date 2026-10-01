import JSP000404Research.ResidualEnlargedLossCollisionGraph
import JSP000404Research.ResidualLossAllActivePairOverlap
import JSP000404Research.ResidualEnlargedCandidateHall
import Mathlib.Tactic

/-!
# Rigidity of a maximal loss vertex with a unique collision neighbour

Work inside an inclusion-minimal deficient core for the enlarged candidate
family.  Let v be projected-loss, assume its completion cube is maximal among
all loss vertices in the core, and suppose v has a unique collision neighbour.

The unique neighbour w must also be projected-loss.  Hence

  card(B_v ∩ B_w) <= card(Q_v) + card(Q_w)
                  <= 2 card(Q_v).

On the other hand minimal deficiency forces

  card(shared_v) >= card(B_v) - 2^k(v) + 1.

Since

  card(B_v) = (a_v+1) card(Q_v),
  2^k(v)    = 2 card(Q_v),

this lower bound is

  (a_v-1) card(Q_v) + 1.

If a_v >= 3, it exceeds 2 card(Q_v), contradicting the pair-overlap upper
bound.  Projected loss with exponent<n already gives a_v>=2, so necessarily

  card(retainedActive(v)) = 2.

Equivalently this unique-neighbour extremal case is forced onto the sharp
top-loss exponent k(v)=n-1.
-/

namespace JSP000404Research
namespace OrderedEdgeColoring

theorem minimal_enlargedCandidate_maxLoss_unique_neighbor_active_card_eq_two
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexpLt : ∀ x, exponent x < n)
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
    (hmaxLoss :
      ∀ z : V,
        z ∈ T →
        z ∈ projectedLossVertices C exponent →
        (retainedCompletionWords C z).card ≤
          (retainedCompletionWords C v).card)
    (hunique :
      ∀ z : V,
        z ∈ T →
        z ≠ v →
        EnlargedBlocksCross C exponent v z →
        z = w) :
    (retainedActive C v).card = 2 := by
  classical
  have hwLoss :
      w ∈ projectedLossVertices C exponent :=
    minimal_enlargedCandidate_loss_unique_neighbor_is_loss
      C exponent hexp honeLoss
      hdef hmin hvT hvLoss (hexpLt v) hunique

  have hsharedSub :
      sharedBlockWords
          (enlargedProjectedCandidateBlock C exponent)
          T v
        ⊆
      enlargedProjectedCandidateBlock C exponent v ∩
        enlargedProjectedCandidateBlock C exponent w :=
    sharedBlockWords_subset_single_neighbor_intersection
      (enlargedProjectedCandidateBlock C exponent)
      hvT
      (by
        intro z hzT hzv hcross
        exact hunique z hzT hzv hcross)

  have hsharedUpper :
      (sharedBlockWords
        (enlargedProjectedCandidateBlock C exponent)
        T v).card
        ≤
      (retainedCompletionWords C v).card +
        (retainedCompletionWords C w).card := by
    have hcard :=
      Finset.card_le_card hsharedSub
    rw [enlargedProjectedCandidateBlock_loss
          C exponent hvLoss,
        enlargedProjectedCandidateBlock_loss
          C exponent hwLoss] at hcard
    have hinter :=
      loss_allActive_pair_intersection_card_le_sum_cubes
        C exponent hexp honeLoss
        hvLoss hwLoss
        (by
          intro hvw
          subst w
          exact hunique v hvT (by simp) (by
            unfold EnlargedBlocksCross
            simp))
    exact hcard.trans hinter

  have hwCubeLe :
      (retainedCompletionWords C w).card ≤
        (retainedCompletionWords C v).card :=
    hmaxLoss w
      (by
        by_contra hwNotT
        have hshared :=
          minimal_enlargedCandidate_loss_shared_nonempty
            C exponent hdef hmin hvT hvLoss (hexpLt v)
        obtain ⟨word,hword⟩ := hshared
        have hdata :=
          sharedBlockWords_has_other_block
            (enlargedProjectedCandidateBlock C exponent) hword
        obtain ⟨_hvWord,z,hzT,hzv,hzWord⟩ := hdata
        have hcross : EnlargedBlocksCross C exponent v z := by
          exact ⟨word,_hvWord,hzWord⟩
        have hzw := hunique z hzT hzv hcross
        subst z
        exact hwNotT hzT)
      hwLoss

  have hsharedUpper2 :
      (sharedBlockWords
        (enlargedProjectedCandidateBlock C exponent)
        T v).card
        ≤
      2 * (retainedCompletionWords C v).card := by
    omega

  have hlocal :
      2 ^ exponent v ≤
        (enlargedProjectedCandidateBlock C exponent v).card := by
    exact enlargedProjectedCandidateBlock_local_capacity
      C exponent hexpLt hexp honeLoss v

  have hsharedLower :=
    minimal_deficient_shared_card_ge_slack_add_one
      (fun x : V => 2 ^ exponent x)
      (enlargedProjectedCandidateBlock C exponent)
      hdef hmin hvT hlocal

  rw [enlargedProjectedCandidateBlock_loss
        C exponent hvLoss,
      allActiveLossCandidateBlock_card,
      projectedLoss_target_eq_two_mul_completion
        C exponent hvLoss] at hsharedLower

  have hactiveGe :
      2 ≤ (retainedActive C v).card :=
    projectedLoss_active_card_ge_two_of_exponent_lt_n
      C exponent hvLoss (hexpLt v)

  by_contra hne
  have hactiveGe3 :
      3 ≤ (retainedActive C v).card := by
    omega
  have hQpos :
      0 < (retainedCompletionWords C v).card := by
    rw [retainedCompletionWords_card]
    positivity
  omega

theorem minimal_enlargedCandidate_maxLoss_unique_neighbor_exponent_eq_n_sub_one
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexpLt : ∀ x, exponent x < n)
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
    (hmaxLoss :
      ∀ z : V,
        z ∈ T →
        z ∈ projectedLossVertices C exponent →
        (retainedCompletionWords C z).card ≤
          (retainedCompletionWords C v).card)
    (hunique :
      ∀ z : V,
        z ∈ T →
        z ≠ v →
        EnlargedBlocksCross C exponent v z →
        z = w) :
    exponent v = n - 1 := by
  have hactive :=
    minimal_enlargedCandidate_maxLoss_unique_neighbor_active_card_eq_two
      C exponent hexpLt hexp honeLoss
      hdef hmin hvT hvLoss hmaxLoss hunique
  have hloss :=
    (mem_projectedLossVertices C exponent v).1 hvLoss
  unfold projectedFree at hloss
  omega

#print axioms minimal_enlargedCandidate_maxLoss_unique_neighbor_active_card_eq_two
#print axioms minimal_enlargedCandidate_maxLoss_unique_neighbor_exponent_eq_n_sub_one

end OrderedEdgeColoring
end JSP000404Research
