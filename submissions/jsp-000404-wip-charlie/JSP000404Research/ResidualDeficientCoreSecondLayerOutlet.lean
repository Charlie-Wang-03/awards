import JSP000404Research.ResidualCommonWordTriangleSecondLayerOutlet
import JSP000404Research.ResidualTripleFibreOutlet
import Mathlib.Tactic

/-!
# Deficient core with common-word second-layer information preserved

The girth-free multiplicity root already says that a deficient enlarged
candidate core either contains a Boolean word covered by at least three core
blocks, or exposes one of the exact/top recursive overloads.

Previously the triple-covered branch was compressed to a high-layer two-loss
pair, discarding the profile of the third carrier.  The common-word triangle
outlet keeps that carrier and therefore yields the exact interface needed by
the planar Q/T/T/T endgame.
-/

namespace JSP000404Research
namespace OrderedEdgeColoring

theorem deficientCore_secondLayer_commonWord_or_recursiveOverload
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexpLt : ∀ x, exponent x < n)
    (hexp : ∀ x, exponent x ≤ n)
    (honeLoss :
      ∀ x, (active C x).card ≤ n - exponent x + 1)
    (htop :
      ((Finset.univ : Finset V).filter
        (fun z => exponent z = n - 1)).card ≤ 1)
    {T : Finset V}
    (hdef :
      BlockDeficient
        (fun x => 2 ^ exponent x)
        (enlargedProjectedCandidateBlock C exponent)
        T) :
    (
      ∃ word : Fin n → Bool,
      ∃ u v w : {x : V // x ∈ T},
        u ≠ v ∧ u ≠ w ∧ v ≠ w ∧
        CommonWordTriangleSecondLayerOutlet
          C exponent T word u v w
    )
    ∨
    (
      ∃ v ∈ T,
        ExactProjectedBudget C exponent v ∧
        ExactSharedOutlet C exponent v
    )
    ∨
    (
      ∃ v ∈ T,
        v ∈ projectedLossVertices C exponent ∧
        exponent v = n - 1 ∧
        (
          sharedBlockWords
            (enlargedProjectedCandidateBlock C exponent)
            T v
          ∩
          retainedCompletionWords C v
        ).Nonempty
    ) := by
  rcases
    deficientCore_tripleFibre_or_recursiveOverload
      C exponent hexpLt hexp honeLoss hdef
    with htriple | hexact | htopShared
  · obtain ⟨word,hthree⟩ := htriple
    obtain ⟨u,v,w,huv,huw,hvw,
      huWord,hvWord,hwWord,hUV,hUW,hVW⟩ :=
      tripleFibre_has_common_word_collision_triangle
        C exponent hthree
    have hout :=
      enlargedCollisionGraph_commonWord_triangle_secondLayer_outlet
        C exponent hexpLt hexp honeLoss htop T
        hUV hUW hVW huWord hvWord hwWord
    exact Or.inl ⟨word,u,v,w,huv,huw,hvw,hout⟩
  · exact Or.inr (Or.inl hexact)
  · exact Or.inr (Or.inr htopShared)

#print axioms deficientCore_secondLayer_commonWord_or_recursiveOverload

end OrderedEdgeColoring
end JSP000404Research
