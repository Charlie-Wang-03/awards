import JSP000404Research.ResidualTwoVertexDeficiencySlack
import Mathlib.Tactic

/-!
# Exact unit defect in a two-centre enlarged Hall obstruction

A two-centre deficient family already has no projected-loss endpoints.
The certified strict-overlap-excess inequality says that overlap must
exceed both vertices' nonnegative slack above their dyadic targets.

If geometric information bounds the intersection of the actual retained
completion cubes by ONE word, the only possible deficit is exactly
ONE word, and BOTH local retained cubes are dyadically saturated.

This is a necessary conditional classification, NOT a proof of the
intersection bound from AngleCap or a solution of the global payment.
-/

namespace JSP000404Research
namespace OrderedEdgeColoring

theorem two_vertex_enlarged_deficiency_unit_intersection_rigidity
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexpLt : ∀ x, exponent x < n)
    (hexp : ∀ x, exponent x ≤ n)
    (honeLoss : ∀ x, (active C x).card ≤ n - exponent x + 1)
    {v w : V}
    (hvw : v ≠ w)
    (hdef :
      BlockDeficient
        (fun x => 2 ^ exponent x)
        (enlargedProjectedCandidateBlock C exponent)
        ({v,w} : Finset V))
    (hInter :
      (retainedCompletionWords C v ∩
        retainedCompletionWords C w).card ≤ 1) :
    (retainedCompletionWords C v).card = 2 ^ exponent v ∧
    (retainedCompletionWords C w).card = 2 ^ exponent w ∧
    (retainedCompletionWords C v ∩
      retainedCompletionWords C w).card = 1 ∧
    (retainedCompletionWords C v ∪
      retainedCompletionWords C w).card + 1 =
        2 ^ exponent v + 2 ^ exponent w := by
  classical
  obtain ⟨hvNonloss, hwNonloss⟩ :=
    two_vertex_enlarged_deficiency_forces_both_nonloss
      C exponent hexpLt hexp honeLoss hvw hdef
  have hvCap :
      2 ^ exponent v ≤ (retainedCompletionWords C v).card := by
    have hcap :=
      enlargedProjectedCandidateBlock_local_capacity
        C exponent hexpLt hexp honeLoss v
    rwa [enlargedProjectedCandidateBlock_nonloss
      C exponent hvNonloss] at hcap
  have hwCap :
      2 ^ exponent w ≤ (retainedCompletionWords C w).card := by
    have hcap :=
      enlargedProjectedCandidateBlock_local_capacity
        C exponent hexpLt hexp honeLoss w
    rwa [enlargedProjectedCandidateBlock_nonloss
      C exponent hwNonloss] at hcap
  have hStrict :=
    two_vertex_enlarged_deficiency_forces_strict_overlap_excess
      C exponent hexpLt hexp honeLoss hvw hdef
  have hCard :=
    Finset.card_union_add_card_inter
      (retainedCompletionWords C v)
      (retainedCompletionWords C w)
  omega

/-- When an overlap of at most one word occurs, at least one
nonsaturated cube rules out a two-centre enlarged Hall defect. -/
theorem two_vertex_enlarged_not_deficient_of_unit_intersection_slack
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexpLt : ∀ x, exponent x < n)
    (hexp : ∀ x, exponent x ≤ n)
    (honeLoss : ∀ x, (active C x).card ≤ n - exponent x + 1)
    {v w : V}
    (hvw : v ≠ w)
    (hInter :
      (retainedCompletionWords C v ∩
        retainedCompletionWords C w).card ≤ 1)
    (hSlack :
      2 ^ exponent v < (retainedCompletionWords C v).card ∨
      2 ^ exponent w < (retainedCompletionWords C w).card) :
    ¬ BlockDeficient
        (fun x => 2 ^ exponent x)
        (enlargedProjectedCandidateBlock C exponent)
        ({v,w} : Finset V) := by
  intro hdef
  obtain ⟨hvSat, hwSat, _, _⟩ :=
    two_vertex_enlarged_deficiency_unit_intersection_rigidity
      C exponent hexpLt hexp honeLoss hvw hdef hInter
  rcases hSlack with hs | hs
  · omega
  · omega

#print axioms two_vertex_enlarged_deficiency_unit_intersection_rigidity
#print axioms two_vertex_enlarged_not_deficient_of_unit_intersection_slack

end OrderedEdgeColoring
end JSP000404Research
