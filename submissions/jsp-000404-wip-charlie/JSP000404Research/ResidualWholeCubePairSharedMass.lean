import JSP000404Research.ResidualQTTTWholeCubeCoreSplit
import JSP000404Research.ResidualEnlargedCandidateBlock
import JSP000404Research.ResidualLossAllActiveCandidateBlock
import JSP000404Research.ResidualPairLocalFlip
import Mathlib.Tactic

/-!
# Two whole shared cubes from a whole-cube Q/T pair

Assume a whole-cube Q/T pair between completion owner s and translated owner v
at an active coordinate c:

  retainedActive(v) = retainedActive(s),
  T_v(c) = Q_s.

Because c is active at v, it is active at s as well.  Since the coordinate
flip is involutive,

  T_s(c) = Q_v.

Hence, when both endpoints are projected-loss vertices, their enlarged
all-active candidate blocks both contain Q_v and Q_s.  The two cubes are
disjoint, because Q_s=T_v(c) and an active translated slice is disjoint from
Q_v.

This yields a quantitative lower bound of two full completion cubes on the
pairwise block intersection.
-/

namespace JSP000404Research
namespace OrderedEdgeColoring

theorem wholeCubeQTPair_completion_swap_of_active
    {V : Type*} [LinearOrder V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    {s v : V} {c : Fin n}
    (hcV : c ∈ retainedActive C v)
    (hwhole : WholeCubeQTPair C s v c) :
    c ∈ retainedActive C s ∧
    translatedCompletionWords C s c =
      retainedCompletionWords C v := by
  rcases hwhole with ⟨hactiveEq,htransEq⟩
  have hcS : c ∈ retainedActive C s := by
    rw [← hactiveEq]
    exact hcV
  refine ⟨hcS,?_⟩
  ext word
  rw [mem_translatedCompletionWords]
  rw [← htransEq]
  rw [mem_translatedCompletionWords]
  simp [flipBoolWordAt_involutive]

theorem retainedCompletion_subset_enlarged_loss
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    {v : V}
    (hvLoss : v ∈ projectedLossVertices C exponent) :
    retainedCompletionWords C v ⊆
      enlargedProjectedCandidateBlock C exponent v := by
  rw [enlargedProjectedCandidateBlock_loss C exponent hvLoss]
  intro word hword
  unfold allActiveLossCandidateBlock
  exact Finset.mem_union_left _ hword

theorem translatedCompletion_subset_enlarged_loss
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    {v : V} {c : Fin n}
    (hvLoss : v ∈ projectedLossVertices C exponent)
    (hc : c ∈ retainedActive C v) :
    translatedCompletionWords C v c ⊆
      enlargedProjectedCandidateBlock C exponent v := by
  rw [enlargedProjectedCandidateBlock_loss C exponent hvLoss]
  intro word hword
  unfold allActiveLossCandidateBlock
  apply Finset.mem_union_right
  unfold allActiveTranslatedWords
  exact Finset.mem_biUnion.mpr ⟨c,hc,hword⟩

theorem wholeCubeQTPair_two_cubes_subset_block_intersection
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    {s v : V} {c : Fin n}
    (hsLoss : s ∈ projectedLossVertices C exponent)
    (hvLoss : v ∈ projectedLossVertices C exponent)
    (hcV : c ∈ retainedActive C v)
    (hwhole : WholeCubeQTPair C s v c) :
    retainedCompletionWords C v ∪ retainedCompletionWords C s
      ⊆
    enlargedProjectedCandidateBlock C exponent v ∩
      enlargedProjectedCandidateBlock C exponent s := by
  obtain ⟨hcS,hswap⟩ :=
    wholeCubeQTPair_completion_swap_of_active C hcV hwhole
  rcases hwhole with ⟨_hactiveEq,htransEq⟩
  intro word hword
  rw [Finset.mem_union] at hword
  rw [Finset.mem_inter]
  rcases hword with hv | hs
  · constructor
    · exact retainedCompletion_subset_enlarged_loss
        C exponent hvLoss hv
    · apply translatedCompletion_subset_enlarged_loss
        C exponent hsLoss hcS
      rw [hswap]
      exact hv
  · constructor
    · apply translatedCompletion_subset_enlarged_loss
        C exponent hvLoss hcV
      rw [htransEq]
      exact hs
    · exact retainedCompletion_subset_enlarged_loss
        C exponent hsLoss hs

theorem wholeCubeQTPair_block_intersection_card_ge_two_cubes
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    {s v : V} {c : Fin n}
    (hsLoss : s ∈ projectedLossVertices C exponent)
    (hvLoss : v ∈ projectedLossVertices C exponent)
    (hcV : c ∈ retainedActive C v)
    (hwhole : WholeCubeQTPair C s v c) :
    2 * (retainedCompletionWords C v).card
      ≤
    (enlargedProjectedCandidateBlock C exponent v ∩
      enlargedProjectedCandidateBlock C exponent s).card := by
  have hsub :=
    wholeCubeQTPair_two_cubes_subset_block_intersection
      C exponent hsLoss hvLoss hcV hwhole
  have hcardSub := Finset.card_le_card hsub

  rcases hwhole with ⟨_hactiveEq,htransEq⟩
  have hdisj :
      Disjoint
        (retainedCompletionWords C v)
        (retainedCompletionWords C s) := by
    have h :=
      translatedCompletionWords_disjoint_original_of_active C hcV
    rw [htransEq] at h
    exact h.symm
  have hcardEq :
      (retainedCompletionWords C s).card =
        (retainedCompletionWords C v).card := by
    rw [← htransEq, translatedCompletionWords_card]

  have hunion :
      (retainedCompletionWords C v ∪
        retainedCompletionWords C s).card
        =
      2 * (retainedCompletionWords C v).card := by
    rw [Finset.card_union_of_disjoint hdisj,hcardEq]
    omega
  rw [hunion] at hcardSub
  exact hcardSub

theorem wholeCubeQTPair_secondLayer_block_intersection_ge_demand
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hn3 : 3 ≤ n)
    {s v : V} {c : Fin n}
    (hsLoss : s ∈ projectedLossVertices C exponent)
    (hvLoss : v ∈ projectedLossVertices C exponent)
    (hvSecond : exponent v = n - 2)
    (hcV : c ∈ retainedActive C v)
    (hwhole : WholeCubeQTPair C s v c) :
    2 ^ (n - 2) ≤
      (enlargedProjectedCandidateBlock C exponent v ∩
        enlargedProjectedCandidateBlock C exponent s).card := by
  have hlossEq :=
    (mem_projectedLossVertices C exponent v).1 hvLoss
  have hfree : projectedFree C v = n - 3 := by
    rw [hvSecond] at hlossEq
    omega
  have hbase :=
    wholeCubeQTPair_block_intersection_card_ge_two_cubes
      C exponent hsLoss hvLoss hcV hwhole
  rw [retainedCompletionWords_card,hfree] at hbase
  have hpow :
      2 * 2 ^ (n - 3) = 2 ^ (n - 2) := by
    have hs : n - 3 + 1 = n - 2 := by omega
    rw [← hs,pow_succ]
    omega
  rw [hpow] at hbase
  exact hbase

#print axioms wholeCubeQTPair_completion_swap_of_active
#print axioms wholeCubeQTPair_two_cubes_subset_block_intersection
#print axioms wholeCubeQTPair_block_intersection_card_ge_two_cubes
#print axioms wholeCubeQTPair_secondLayer_block_intersection_ge_demand

end OrderedEdgeColoring
end JSP000404Research
