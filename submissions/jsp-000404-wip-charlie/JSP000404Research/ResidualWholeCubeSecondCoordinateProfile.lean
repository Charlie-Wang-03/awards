import JSP000404Research.ResidualWholeCubeSecondCoordinate
import JSP000404Research.ResidualWholeCubeSecondCoordinateCore
import JSP000404Research.ProjectionEnlargedCandidateHall
import Mathlib.Tactic

/-!
# Profile reduction of the second-coordinate whole-cube augmentation

A WholeCubeThirdSourceWitness is not merely an extra core neighbour.
The witness word lies in a translated slice at a second active coordinate
d != c of the whole-cube partner v.

Classify the third source w by the standard projected profile.  Every branch
except the second-layer projected-loss branch is already one of the standard
closed outlets: strict surplus, exact projected budget, top loss, or deep
loss.  Hence the only genuinely new frontier is a second-layer loss vertex w
carrying the second-coordinate translated collision.
-/

namespace JSP000404Research
namespace OrderedEdgeColoring

theorem wholeCubeThirdSource_profile_reduction
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexpLt : ∀ q, exponent q < n)
    (hexp : ∀ q, exponent q ≤ n)
    (honeLoss :
      ∀ q, (active C q).card ≤ n - exponent q + 1)
    {T : Finset V}
    {s v : V} {c : Fin n}
    (hvLoss : v ∈ projectedLossVertices C exponent)
    (hwhole : WholeCubeQTPair C s v c)
    (hwit : WholeCubeThirdSourceWitness C exponent T s v) :
    (
      ∃ q : V,
        1 ≤ dyadicProfileSurplus
          exponent (projectedFree C) q
    )
    ∨
    (
      ∃ q : V,
        ExactProjectedBudget C exponent q
    )
    ∨
    (
      ∃ q : V,
        q ∈ projectedLossVertices C exponent ∧
        exponent q = n - 1
    )
    ∨
    (
      ∃ q : V,
        q ∈ projectedLossVertices C exponent ∧
        exponent q + 3 ≤ n
    )
    ∨
    WholeCubeSecondCoordinateSecondLayerWitness
      C exponent T s v c := by
  obtain ⟨word,w,d,hdActive,hdc,hdWord,
      hwBlock,hwT,hwNeV,hwNeS⟩ :=
    wholeCubeThirdSourceWitness_has_other_translated_coordinate
      C exponent hvLoss hwhole hwit

  rcases
    projectedProfile_strict_exact_or_loss
      C exponent hexp honeLoss w
    with hwStrict | hwExact | hwLoss
  · exact Or.inl
      ⟨w,
        projected_strict_surplus_at_least_one
          exponent (projectedFree C) hwStrict⟩
  · exact Or.inr (Or.inl ⟨w,hwExact⟩)
  · rcases exponent_top_second_or_deep
        exponent (hexpLt w)
      with hwTop | hwSecond | hwDeep
    · exact Or.inr (Or.inr (Or.inl
        ⟨w,hwLoss,hwTop⟩))
    · exact Or.inr (Or.inr (Or.inr (Or.inr
        ⟨word,w,d,
          hdActive,hdc,hdWord,hwBlock,
          hwT,hwNeV,hwNeS,hwLoss,hwSecond⟩)))
    · exact Or.inr (Or.inr (Or.inr (Or.inl
        ⟨w,hwLoss,hwDeep⟩)))

#print axioms wholeCubeThirdSource_profile_reduction

end OrderedEdgeColoring
end JSP000404Research
