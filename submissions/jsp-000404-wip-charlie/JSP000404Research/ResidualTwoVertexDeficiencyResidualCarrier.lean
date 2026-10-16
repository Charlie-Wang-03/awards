import JSP000404Research.ResidualEnlargedTwoVertexDeficiency
import JSP000404Research.ResidualCompletionMultiplicity
import Mathlib.Tactic

/-!
# A two-centre enlarged Hall defect must be a genuine residual edge

Existing pair-capacity results rule out projected-loss endpoints in a
two-vertex deficient enlarged candidate family.  At non-loss vertices,
the enlarged candidate block is exactly the retained completion cube.

Therefore a two-centre deficient family forces an overlapping pair
of retained completion cubes.  Retained-cube overlap on distinct
vertices is possible only across an actual residual edge.

This is a certified necessary classification, NOT an exclusion
of all two-vertex deficient cores.
-/

namespace JSP000404Research
namespace OrderedEdgeColoring

theorem two_vertex_enlarged_deficiency_forces_residual_carrier
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
    (v < w ∧ IsResidual C v w) ∨
      (w < v ∧ IsResidual C w v) := by
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
  have hoverlap :
      (retainedCompletionWords C v ∩
        retainedCompletionWords C w).Nonempty := by
    by_contra hnone
    have hdisj :
        Disjoint (retainedCompletionWords C v)
          (retainedCompletionWords C w) :=
      Finset.not_nonempty_iff_eq_empty.mp hnone |>
        Finset.disjoint_iff_inter_eq_empty.mpr
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
    unfold BlockDeficient at hdef
    rw [hsum, hblocks, Finset.card_union_of_disjoint hdisj] at hdef
    omega
  obtain ⟨word,hword⟩ := hoverlap
  exact retainedCompletion_overlap_forces_residual
    C hvw (Finset.mem_inter.mp hword).1
      (Finset.mem_inter.mp hword).2

#print axioms two_vertex_enlarged_deficiency_forces_residual_carrier

end OrderedEdgeColoring
end JSP000404Research
