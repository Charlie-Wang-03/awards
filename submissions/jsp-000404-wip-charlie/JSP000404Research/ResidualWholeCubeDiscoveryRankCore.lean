import JSP000404Research.ResidualSecondLayerProjectedLossCard
import JSP000404Research.WholeCubeQTPairCore
import Mathlib.Tactic

/-!
# Lightweight whole-cube discovery rank core

For a fixed second-layer projected-loss endpoint v, discovered whole-cube
coordinates form a subset of its three retained-active coordinates.  Inserting
a genuinely new coordinate therefore strictly decreases the rank

  3 - card(coords).

This file deliberately excludes saturation/minimal-core theorems.
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
  rw [Finset.card_insert_of_notMem hd]
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
    secondLayer_projectedLoss_retainedActive_card_eq_three_core
      C exponent hvLoss hvSecond
  exact (Finset.card_le_card hsub).trans_eq hactive

theorem profiled_TQ_rematch_repeat_or_discovery_progress
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    {v w : V} {d : Fin n}
    (hvLoss : v ∈ projectedLossVertices C exponent)
    (hvSecond : exponent v = n - 2)
    (hdV : d ∈ retainedActive C v)
    (_hwLoss : w ∈ projectedLossVertices C exponent)
    (_hwhole : WholeCubeQTPair C w v d)
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
    have hle :=
      discovered_coordinates_card_le_three_of_subset_secondLayerActive
        C exponent hvLoss hvSecond hcoords
    have hcard : coords.card < 3 := by
      by_contra hnot
      have heq : coords.card = 3 := by omega
      have hactiveCard :
          (retainedActive C v).card = 3 :=
        secondLayer_projectedLoss_retainedActive_card_eq_three_core
          C exponent hvLoss hvSecond
      have hEq :
          coords = retainedActive C v :=
        Finset.eq_of_subset_of_card_le
          hcoords (by simpa [heq,hactiveCard])
      exact hd (by rw [hEq]; exact hdV)
    exact wholeCubeDiscoveryRank_lt_of_insert_new hcard hd

#print axioms wholeCubeDiscoveryRank_lt_of_insert_new
#print axioms profiled_TQ_rematch_repeat_or_discovery_progress

end OrderedEdgeColoring
end JSP000404Research
