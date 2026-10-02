import JSP000404Research.ResidualWholeCubePartnerSaturation
import JSP000404Research.ResidualWholeCubePartnerMultiplicity
import JSP000404Research.ResidualThreeWholeCubeMinimalCoreCollapse
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

def WholeCubeDiscoveredCoordinates
    {n : ℕ}
    (coords : Finset (Fin n)) : Prop := True

def wholeCubeDiscoveryRank
    {n : ℕ}
    (coords : Finset (Fin n)) : ℕ :=
  3 - coords.card

theorem wholeCubeDiscoveryRank_lt_of_insert_new
    {n : ℕ}
    {coords : Finset (Fin n)}
    {d : Fin n}
    (hcard : coords.card < 3)
    (hd : d ∉ coords) :
    wholeCubeDiscoveryRank (insert d coords) <
      wholeCubeDiscoveryRank coords := by
  unfold wholeCubeDiscoveryRank
  rw [Finset.card_insert_of_not_mem hd]
  omega

theorem discovered_coordinates_card_le_three_of_subset_secondLayerActive
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    {v : V}
    (hvLoss : v ∈ projectedLossVertices C exponent)
    (hvSecond : exponent v = n - 2)
    {coords : Finset (Fin n)}
    (hsub : coords ⊆ retainedActive C v) :
    coords.card ≤ 3 := by
  have hactive :
      (retainedActive C v).card = 3 :=
    secondLayer_projectedLoss_retainedActive_card_eq_three
      C exponent (by
        have heq :=
          secondLayerLoss_retainedActive_card_eq_three
            C exponent hvLoss hvSecond
        exact heq)
      hvLoss hvSecond
  exact (Finset.card_le_card hsub).trans_eq hactive

/-- A profile-preserving lossless T/Q rematch at a fixed second-layer endpoint
is either a repeat of a discovered coordinate or strictly decreases the
discovery rank after inserting its new coordinate. -/
theorem profiled_TQ_rematch_repeat_or_discovery_progress
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    {v w : V} {d : Fin n}
    (hvLoss : v ∈ projectedLossVertices C exponent)
    (hvSecond : exponent v = n - 2)
    (hdV : d ∈ retainedActive C v)
    (hwLoss : w ∈ projectedLossVertices C exponent)
    (hwhole : WholeCubeQTPair C w v d)
    (coords : Finset (Fin n))
    (hcoords :
      coords ⊆ retainedActive C v) :
    d ∈ coords
    ∨
    (
      d ∉ coords ∧
      wholeCubeDiscoveryRank (insert d coords) <
        wholeCubeDiscoveryRank coords
    ) := by
  by_cases hd : d ∈ coords
  · exact Or.inl hd
  · right
    refine ⟨hd,?_⟩
    have hcard :
        coords.card < 3 := by
      have hle :=
        discovered_coordinates_card_le_three_of_subset_secondLayerActive
          C exponent hvLoss hvSecond hcoords
      by_contra hnot
      have heq : coords.card = 3 := by omega
      have hactiveCard :
          (retainedActive C v).card = 3 :=
        secondLayerLoss_retainedActive_card_eq_three
          C exponent hvLoss hvSecond
      have hEq :
          coords = retainedActive C v :=
        Finset.eq_of_subset_of_card_le
          hcoords (by simpa [heq,hactiveCard])
      exact hd (by rw [hEq]; exact hdV)
    exact wholeCubeDiscoveryRank_lt_of_insert_new hcard hd

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

#print axioms wholeCubeDiscoveryRank_lt_of_insert_new
#print axioms profiled_TQ_rematch_repeat_or_discovery_progress
#print axioms saturated_discovery_rematch_is_repeat

end OrderedEdgeColoring
end JSP000404Research
