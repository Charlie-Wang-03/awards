import JSP000404Research.ResidualWholeCubeDiscoveryRankCore
import JSP000404Research.ResidualWholeCubePartnerSaturation
import Mathlib.Tactic

/-!
# Finite discovery state for lossless whole-cube T/Q rematches

For a fixed second-layer projected-loss translated endpoint v, a projected-loss
WholeCubeQTPair state is determined by its active owner coordinate: each
coordinate has at most one projected-loss partner, and v has exactly three
active coordinates.

We package a finite set of already-discovered whole-cube coordinates.  A new
profile-preserving T/Q rematch is therefore either

* a repeat at an already-discovered coordinate (contractible), or
* a genuinely new coordinate, increasing discovered-state cardinality.

The latter can occur at most three times.  Once all three active coordinates
are discovered, the three partners exhaust all further projected-loss
rematches; moreover, if the source and all three partners lie in a minimal
deficient core, the core collapses to the explicit four-vertex 7-of-8
obstruction.
-/

namespace JSP000404Research
namespace OrderedEdgeColoring

/-- If all three active coordinates have already been discovered, any further
profile-preserving whole-cube rematch repeats one of those three exact
coordinate/partner states. -/
theorem saturated_discovery_rematch_is_repeat
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexp : ∀ q, exponent q ≤ n)
    (honeLoss :
      ∀ q, (active C q).card ≤ n - exponent q + 1)
    {v s₁ s₂ s₃ w : V}
    {c₁ c₂ c₃ d : Fin n}
    (hactive :
      retainedActive C v = {c₁,c₂,c₃})
    (hs1Loss : s₁ ∈ projectedLossVertices C exponent)
    (hs2Loss : s₂ ∈ projectedLossVertices C exponent)
    (hs3Loss : s₃ ∈ projectedLossVertices C exponent)
    (hwLoss : w ∈ projectedLossVertices C exponent)
    (h₁ : WholeCubeQTPair C s₁ v c₁)
    (h₂ : WholeCubeQTPair C s₂ v c₂)
    (h₃ : WholeCubeQTPair C s₃ v c₃)
    (hdV : d ∈ retainedActive C v)
    (hw : WholeCubeQTPair C w v d) :
    (d = c₁ ∧ w = s₁)
    ∨ (d = c₂ ∧ w = s₂)
    ∨ (d = c₃ ∧ w = s₃) :=
  threeWholeCubePartners_exhaust_projectedLoss_rematches
    C exponent hexp honeLoss
    hactive hs1Loss hs2Loss hs3Loss hwLoss
    h₁ h₂ h₃ hdV hw

#print axioms saturated_discovery_rematch_is_repeat

end OrderedEdgeColoring
end JSP000404Research
