import JSP000404Research.ResidualEnlargedCandidateBlock
import JSP000404Research.WeightedBlockHallOutlet
import JSP000404Research.MinimalBlockDeficiency
import JSP000404Research.MinimalBlockSharedDeficit
import Mathlib.Tactic

/-!
# Weighted Hall reduction for the enlarged projected candidate family

Use the enlarged candidate family

  non-loss: Q_v,
  loss:     Q_v union all active one-coordinate translates.

If every vertex subset satisfies weighted block expansion, the dyadic target
capacity follows immediately from WeightedBlockHallOutlet.

If expansion fails, choose an inclusion-minimal deficient vertex set T.
MinimalBlockSharedDeficit then converts local block slack into forced
collisions.

At a projected-loss vertex v with exponent(v)<n, the enlarged block has at
least one whole completion cube Q_v of slack beyond its target.  Hence in a
minimal deficient core,

  card(shared(v,T)) >= card(Q_v) + 1.

This quantitative +1 is stronger than the canonical single-flip block, whose
loss block has zero local slack.
-/

namespace JSP000404Research
namespace OrderedEdgeColoring

theorem exponent_capacity_of_enlargedProjectedCandidate_expansion
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hExpansion :
      ∀ S : Finset V,
        (∑ v ∈ S, 2 ^ exponent v) ≤
          (S.biUnion
            (enlargedProjectedCandidateBlock C exponent)).card) :
    (∑ v : V, 2 ^ exponent v) ≤ 2 ^ n := by
  exact dyadic_capacity_of_vertex_block_expansion
    exponent
    (enlargedProjectedCandidateBlock C exponent)
    hExpansion

theorem exists_minimal_enlargedCandidate_deficient_core
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hfail :
      ¬ ∀ S : Finset V,
        (∑ v ∈ S, 2 ^ exponent v) ≤
          (S.biUnion
            (enlargedProjectedCandidateBlock C exponent)).card) :
    ∃ T : Finset V,
      T.Nonempty ∧
      BlockDeficient
        (fun v => 2 ^ exponent v)
        (enlargedProjectedCandidateBlock C exponent)
        T ∧
      ∀ U : Finset V,
        U ⊂ T →
        ¬ BlockDeficient
          (fun v => 2 ^ exponent v)
          (enlargedProjectedCandidateBlock C exponent)
          U := by
  classical
  push_neg at hfail
  obtain ⟨S,hS⟩ := hfail
  have hSdef :
      BlockDeficient
        (fun v => 2 ^ exponent v)
        (enlargedProjectedCandidateBlock C exponent)
        S := by
    exact hS
  obtain ⟨T,hTS,hTdef,hTmin⟩ :=
    exists_minimal_deficient_subset
      (fun v : V => 2 ^ exponent v)
      (enlargedProjectedCandidateBlock C exponent)
      hSdef
  have hnonempty : T.Nonempty := by
    apply deficient_set_nonempty_of_positive_demands
      (fun v : V => 2 ^ exponent v)
      (enlargedProjectedCandidateBlock C exponent)
      (fun v => by positivity)
      hTdef
  exact ⟨T,hnonempty,hTdef,hTmin⟩

theorem minimal_enlargedCandidate_loss_shared_card_ge_cube_add_one
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    {T : Finset V}
    (hdef :
      BlockDeficient
        (fun v => 2 ^ exponent v)
        (enlargedProjectedCandidateBlock C exponent)
        T)
    (hmin :
      ∀ U : Finset V,
        U ⊂ T →
        ¬ BlockDeficient
          (fun v => 2 ^ exponent v)
          (enlargedProjectedCandidateBlock C exponent)
          U)
    {v : V}
    (hvT : v ∈ T)
    (hvLoss : v ∈ projectedLossVertices C exponent)
    (hvLt : exponent v < n) :
    (retainedCompletionWords C v).card + 1 ≤
      (sharedBlockWords
        (enlargedProjectedCandidateBlock C exponent)
        T v).card := by
  have hlocal :
      2 ^ exponent v ≤
        (enlargedProjectedCandidateBlock C exponent v).card := by
    have hplus :=
      enlargedProjectedCandidateBlock_loss_slack
        C exponent hvLoss hvLt
    omega
  have hshared :=
    minimal_deficient_shared_card_ge_slack_add_one
      (fun x : V => 2 ^ exponent x)
      (enlargedProjectedCandidateBlock C exponent)
      hdef hmin hvT hlocal
  have hslack :=
    enlargedProjectedCandidateBlock_loss_slack
      C exponent hvLoss hvLt
  omega

theorem minimal_enlargedCandidate_loss_shared_nonempty
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    {T : Finset V}
    (hdef :
      BlockDeficient
        (fun v => 2 ^ exponent v)
        (enlargedProjectedCandidateBlock C exponent)
        T)
    (hmin :
      ∀ U : Finset V,
        U ⊂ T →
        ¬ BlockDeficient
          (fun v => 2 ^ exponent v)
          (enlargedProjectedCandidateBlock C exponent)
          U)
    {v : V}
    (hvT : v ∈ T)
    (hvLoss : v ∈ projectedLossVertices C exponent)
    (hvLt : exponent v < n) :
    (sharedBlockWords
      (enlargedProjectedCandidateBlock C exponent)
      T v).Nonempty := by
  have hbound :=
    minimal_enlargedCandidate_loss_shared_card_ge_cube_add_one
      C exponent hdef hmin hvT hvLoss hvLt
  apply Finset.card_pos.mp
  omega

#print axioms exponent_capacity_of_enlargedProjectedCandidate_expansion
#print axioms minimal_enlargedCandidate_loss_shared_card_ge_cube_add_one

end OrderedEdgeColoring
end JSP000404Research
