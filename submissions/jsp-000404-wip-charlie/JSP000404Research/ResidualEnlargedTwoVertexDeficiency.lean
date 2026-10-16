import JSP000404Research.ResidualEnlargedPairLossHall
import JSP000404Research.MinimalBlockDeficiency
import Mathlib.Tactic

/-!
# Two-centre deficient enlarged-candidate sets contain no projected losses

By the exact pairwise loss capacity theorem, a two-vertex weighted
Hall deficient set under one-layer residual hypotheses must consist
of two non-loss vertices. This connects the pairwise cube-intersection
lemma to the actual finite minimal-Hall obstruction predicate.
-/

namespace JSP000404Research
namespace OrderedEdgeColoring

theorem two_vertex_enlarged_deficiency_forces_both_nonloss
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
    v ∉ projectedLossVertices C exponent ∧
    w ∉ projectedLossVertices C exponent := by
  classical
  have hno :
      ¬ (v ∈ projectedLossVertices C exponent ∨
         w ∈ projectedLossVertices C exponent) := by
    intro hsome
    have hpair :=
      enlargedCandidate_pair_capacity_of_one_loss
        C exponent hexpLt hexp honeLoss hvw hsome
    have hsum :
        (∑ x ∈ ({v,w} : Finset V), 2 ^ exponent x) =
          2 ^ exponent v + 2 ^ exponent w := by
      simp [hvw, hvw.symm]
    have hunion :
        (({v,w} : Finset V).biUnion
          (enlargedProjectedCandidateBlock C exponent)) =
        enlargedProjectedCandidateBlock C exponent v ∪
          enlargedProjectedCandidateBlock C exponent w := by
      ext word
      constructor
      · intro hword
        obtain ⟨x,hx,hxword⟩ := Finset.mem_biUnion.mp hword
        have hxcases : x = v ∨ x = w := by
          simpa only [Finset.mem_insert, Finset.mem_singleton] using hx
        rcases hxcases with rfl | rfl
        · exact Finset.mem_union_left _ hxword
        · exact Finset.mem_union_right _ hxword
      · intro hword
        rcases Finset.mem_union.mp hword with hvword | hwword
        · exact Finset.mem_biUnion.mpr ⟨v,by simp,hvword⟩
        · exact Finset.mem_biUnion.mpr ⟨w,by simp,hwword⟩
    unfold BlockDeficient at hdef
    rw [hsum,hunion] at hdef
    omega
  exact not_or.mp hno

#print axioms two_vertex_enlarged_deficiency_forces_both_nonloss

end OrderedEdgeColoring
end JSP000404Research
