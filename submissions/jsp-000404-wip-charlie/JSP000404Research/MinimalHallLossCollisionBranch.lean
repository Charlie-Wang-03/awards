import JSP000404Research.ResidualEnlargedCandidateHall
import JSP000404Research.ResidualLossAllActiveIntersection
import Mathlib.Tactic

/-!
# Branching of genuine loss vertices in minimal weighted Hall obstructions

For a projected-loss centre v with exponent(v)<n in an inclusion-minimal
deficient enlarged-candidate family, the shared words of its enlarged
block have cardinality at least |Q_v|+1.

An individual non-loss blocker w can capture no more than |Q_v| words
of the enlarged block of v. Therefore a single non-loss blocker cannot
account for all shared words at v.

Consequently, every such vertex must collide either with another loss
vertex, or with at least two DISTINCT non-loss vertices. This is a
local branching obstruction, not a global Hall expansion theorem.
-/

namespace JSP000404Research
namespace OrderedEdgeColoring

/-- A minimal deficient loss vertex cannot have all of its shared
words captured by just one external non-loss completion cube. -/
theorem minimal_loss_shared_not_subset_single_nonloss
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexp : ∀ i, exponent i ≤ n)
    (hone : ∀ i, (active C i).card ≤ n - exponent i + 1)
    {T : Finset V}
    (hdef : BlockDeficient
      (fun i => 2 ^ exponent i)
      (enlargedProjectedCandidateBlock C exponent) T)
    (hmin : ∀ U : Finset V, U ⊂ T →
      ¬ BlockDeficient
        (fun i => 2 ^ exponent i)
        (enlargedProjectedCandidateBlock C exponent) U)
    {v w : V}
    (hvT : v ∈ T)
    (hvLoss : v ∈ projectedLossVertices C exponent)
    (hvLt : exponent v < n)
    (hvw : v ≠ w)
    (hwNonloss : w ∉ projectedLossVertices C exponent) :
    ¬ sharedBlockWords
        (enlargedProjectedCandidateBlock C exponent) T v
      ⊆ enlargedProjectedCandidateBlock C exponent w := by
  classical
  intro hsub
  have hbig :=
    minimal_enlargedCandidate_loss_shared_card_ge_cube_add_one
      C exponent hdef hmin hvT hvLoss hvLt
  have hsubInter :
      sharedBlockWords
          (enlargedProjectedCandidateBlock C exponent) T v
        ⊆
      enlargedProjectedCandidateBlock C exponent v ∩
        enlargedProjectedCandidateBlock C exponent w := by
    intro word hword
    exact Finset.mem_inter.mpr
      ⟨(Finset.mem_inter.mp hword).1, hsub hword⟩
  have hcard :=
    Finset.card_le_card hsubInter
  have hcapt :
      (enlargedProjectedCandidateBlock C exponent v ∩
        enlargedProjectedCandidateBlock C exponent w).card
        ≤ (retainedCompletionWords C v).card := by
    rw [enlargedProjectedCandidateBlock_loss C exponent hvLoss,
      enlargedProjectedCandidateBlock_nonloss C exponent hwNonloss]
    exact allActiveLossCandidateBlock_inter_blocker_card_le_cube
      C exponent hexp hone hvLoss hvw
  omega

/-- Either a loss neighbour or two distinct non-loss neighbours
must intersect the enlarged block at a minimal deficient loss vertex.
Both alternatives include explicit nonempty overlap certificates. -/
theorem minimal_loss_neighbour_is_loss_or_two_nonloss
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexp : ∀ i, exponent i ≤ n)
    (hone : ∀ i, (active C i).card ≤ n - exponent i + 1)
    {T : Finset V}
    (hdef : BlockDeficient
      (fun i => 2 ^ exponent i)
      (enlargedProjectedCandidateBlock C exponent) T)
    (hmin : ∀ U : Finset V, U ⊂ T →
      ¬ BlockDeficient
        (fun i => 2 ^ exponent i)
        (enlargedProjectedCandidateBlock C exponent) U)
    {v : V}
    (hvT : v ∈ T)
    (hvLoss : v ∈ projectedLossVertices C exponent)
    (hvLt : exponent v < n) :
    (∃ w : V, w ∈ T ∧ w ≠ v ∧
       w ∈ projectedLossVertices C exponent ∧
       (enlargedProjectedCandidateBlock C exponent v ∩
         enlargedProjectedCandidateBlock C exponent w).Nonempty)
    ∨
    (∃ w z : V, w ∈ T ∧ z ∈ T ∧
       w ≠ v ∧ z ≠ v ∧ w ≠ z ∧
       w ∉ projectedLossVertices C exponent ∧
       z ∉ projectedLossVertices C exponent ∧
       (enlargedProjectedCandidateBlock C exponent v ∩
         enlargedProjectedCandidateBlock C exponent w).Nonempty ∧
       (enlargedProjectedCandidateBlock C exponent v ∩
         enlargedProjectedCandidateBlock C exponent z).Nonempty) := by
  classical
  let B := enlargedProjectedCandidateBlock C exponent
  let shared := sharedBlockWords B T v
  have hbig :=
    minimal_enlargedCandidate_loss_shared_card_ge_cube_add_one
      C exponent hdef hmin hvT hvLoss hvLt
  have hpositive : 0 < shared.card := by
    dsimp [shared]
    omega
  obtain ⟨x, hx⟩ := Finset.card_pos.mp hpositive
  obtain ⟨hxB, hxOther⟩ :=
    Finset.mem_inter.mp hx
  obtain ⟨w, hwErase, hxw⟩ :=
    Finset.mem_biUnion.mp hxOther
  have hwT : w ∈ T := (Finset.mem_erase.mp hwErase).2
  have hwv : w ≠ v := (Finset.mem_erase.mp hwErase).1
  have hwOverlap :
      (B v ∩ B w).Nonempty := by
    exact ⟨x, Finset.mem_inter.mpr ⟨hxB, hxw⟩⟩
  by_cases hwLoss : w ∈ projectedLossVertices C exponent
  · exact Or.inl ⟨w, hwT, hwv, hwLoss, hwOverlap⟩
  · have hNotSubset :
        ¬ shared ⊆ B w :=
      minimal_loss_shared_not_subset_single_nonloss
        C exponent hexp hone hdef hmin
        hvT hvLoss hvLt (Ne.symm hwv) hwLoss
    obtain ⟨y, hyShared, hyNotW⟩ :=
      Finset.not_subset.mp hNotSubset
    obtain ⟨hyB, hyOther⟩ :=
      Finset.mem_inter.mp hyShared
    obtain ⟨z, hzErase, hyz⟩ :=
      Finset.mem_biUnion.mp hyOther
    have hzT : z ∈ T := (Finset.mem_erase.mp hzErase).2
    have hzv : z ≠ v := (Finset.mem_erase.mp hzErase).1
    have hwz : w ≠ z := by
      intro heq
      apply hyNotW
      exact heq ▸ hyz
    have hzOverlap :
        (B v ∩ B z).Nonempty := by
      exact ⟨y, Finset.mem_inter.mpr ⟨hyB, hyz⟩⟩
    by_cases hzLoss : z ∈ projectedLossVertices C exponent
    · exact Or.inl ⟨z, hzT, hzv, hzLoss, hzOverlap⟩
    · exact Or.inr
        ⟨w, z, hwT, hzT, hwv, hzv, hwz,
         hwLoss, hzLoss, hwOverlap, hzOverlap⟩

#print axioms minimal_loss_shared_not_subset_single_nonloss
#print axioms minimal_loss_neighbour_is_loss_or_two_nonloss

end OrderedEdgeColoring
end JSP000404Research
