import JSP000404Research.ResidualTwoVertexDeficiencyResidualCarrier
import Mathlib.Tactic

/-!
# Exact overlap excess forced by a deficient two-centre enlarged Hall core

A deficient pair is not explained merely by the existence of a residual
edge.  Its two retained completion cubes must overlap by strictly more
than the sum of their individual cardinality slack above the two
dyadic demands.

The proof starts with the already kernel-checked exclusion of all
projected-loss endpoints.  It then identifies enlarged candidate blocks
with the original retained cubes and uses the exact finite-set union
identity.  No disjointness across other centres is assumed.

This is a necessary local condition, not a global Hall or payment theorem.
-/

namespace JSP000404Research
namespace OrderedEdgeColoring

theorem two_vertex_enlarged_deficiency_forces_strict_overlap_excess
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
        ({v,w} : Finset V)) :
    (retainedCompletionWords C v ∩
      retainedCompletionWords C w).card +
        (2 ^ exponent v + 2 ^ exponent w) >
      (retainedCompletionWords C v).card +
        (retainedCompletionWords C w).card := by
  classical
  obtain ⟨hvNonloss, hwNonloss⟩ :=
    two_vertex_enlarged_deficiency_forces_both_nonloss
      C exponent hexpLt hexp honeLoss hvw hdef
  have hsum :
      (∑ x ∈ ({v,w} : Finset V), 2 ^ exponent x) =
        2 ^ exponent v + 2 ^ exponent w := by
    simp [hvw, hvw.symm]
  have hblocks :
      (({v,w} : Finset V).biUnion
        (enlargedProjectedCandidateBlock C exponent)) =
        retainedCompletionWords C v ∪
          retainedCompletionWords C w := by
    ext word
    simp only [Finset.mem_biUnion, Finset.mem_insert,
      Finset.mem_singleton, Finset.mem_union]
    constructor
    · rintro ⟨x, hx, hword⟩
      rcases hx with rfl | rfl
      · left
        simpa [enlargedProjectedCandidateBlock_nonloss
          C exponent hvNonloss] using hword
      · right
        simpa [enlargedProjectedCandidateBlock_nonloss
          C exponent hwNonloss] using hword
    · intro hword
      rcases hword with hvWord | hwWord
      · refine ⟨v, Or.inl rfl, ?_⟩
        simpa [enlargedProjectedCandidateBlock_nonloss
          C exponent hvNonloss] using hvWord
      · refine ⟨w, Or.inr rfl, ?_⟩
        simpa [enlargedProjectedCandidateBlock_nonloss
          C exponent hwNonloss] using hwWord
  have hcard :=
    Finset.card_union_add_card_inter
      (retainedCompletionWords C v)
      (retainedCompletionWords C w)
  unfold BlockDeficient at hdef
  rw [hsum, hblocks] at hdef
  omega

/-- A numerical bound on retained-cube overlap excludes a two-centre
enlarged Hall defect, even when the two centres form a residual edge. -/
theorem two_vertex_enlarged_not_deficient_of_overlap_slack
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexpLt : ∀ x, exponent x < n)
    (hexp : ∀ x, exponent x ≤ n)
    (honeLoss : ∀ x, (active C x).card ≤ n - exponent x + 1)
    {v w : V}
    (hvw : v ≠ w)
    (hOverlap :
      (retainedCompletionWords C v ∩
        retainedCompletionWords C w).card +
          (2 ^ exponent v + 2 ^ exponent w) ≤
        (retainedCompletionWords C v).card +
          (retainedCompletionWords C w).card) :
    ¬ BlockDeficient
        (fun x => 2 ^ exponent x)
        (enlargedProjectedCandidateBlock C exponent)
        ({v,w} : Finset V) := by
  intro hdef
  have hstrict :=
    two_vertex_enlarged_deficiency_forces_strict_overlap_excess
      C exponent hexpLt hexp honeLoss hvw hdef
  omega

#print axioms two_vertex_enlarged_deficiency_forces_strict_overlap_excess
#print axioms two_vertex_enlarged_not_deficient_of_overlap_slack

end OrderedEdgeColoring
end JSP000404Research
