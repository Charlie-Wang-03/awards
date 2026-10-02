import JSP000404Research.ResidualWholeCubeDiscoveryRank
import JSP000404Research.ResidualTranslatedCubeRematchQuotient
import JSP000404Research.ResidualWeightedRecursionRank
import Mathlib.Tactic

/-!
# Unified natural rank for non-contractible whole-cube recursion

After quotienting exact rematches, the only genuine progress modes are:

* payload decrease;
* same payload with discovery of a new whole-cube coordinate.

A second-layer source has at most three discovered coordinates.  Therefore

  R(payload,coords) = 4*payload + (3 - card(coords))

strictly decreases in either mode.  The coefficient four is the smallest
uniform coefficient that dominates an arbitrary reset of the discovery
component from 0 back to 3 after a payload decrease.
-/

namespace JSP000404Research
namespace OrderedEdgeColoring

def wholeCubeProgressRank
    {n : ℕ}
    (payload : ℕ)
    (coords : Finset (Fin n)) : ℕ :=
  4 * payload + wholeCubeDiscoveryRank coords

theorem wholeCubeDiscoveryRank_le_three
    {n : ℕ}
    (coords : Finset (Fin n)) :
    wholeCubeDiscoveryRank coords ≤ 3 := by
  unfold wholeCubeDiscoveryRank
  omega

theorem wholeCubeProgressRank_lt_of_payload_lt
    {n : ℕ}
    {payload payload' : ℕ}
    {coords coords' : Finset (Fin n)}
    (hpayload : payload' < payload) :
    wholeCubeProgressRank payload' coords' <
      wholeCubeProgressRank payload coords := by
  unfold wholeCubeProgressRank
  have hrank' :
      wholeCubeDiscoveryRank coords' ≤ 3 :=
    wholeCubeDiscoveryRank_le_three coords'
  have hrank :
      0 ≤ wholeCubeDiscoveryRank coords :=
    Nat.zero_le _
  omega

theorem wholeCubeProgressRank_lt_of_discovery
    {n : ℕ}
    {payload : ℕ}
    {coords : Finset (Fin n)}
    {d : Fin n}
    (hprogress :
      wholeCubeDiscoveryRank (insert d coords) <
        wholeCubeDiscoveryRank coords) :
    wholeCubeProgressRank payload (insert d coords) <
      wholeCubeProgressRank payload coords := by
  unfold wholeCubeProgressRank
  omega

theorem wholeCubeProgressRank_lt_of_progress
    {n : ℕ}
    {payload payload' : ℕ}
    {coords coords' : Finset (Fin n)}
    (hprogress :
      payload' < payload
      ∨
      (payload' = payload ∧
        wholeCubeDiscoveryRank coords' <
          wholeCubeDiscoveryRank coords)) :
    wholeCubeProgressRank payload' coords' <
      wholeCubeProgressRank payload coords := by
  rcases hprogress with hpayload | ⟨rfl,hdisc⟩
  · exact wholeCubeProgressRank_lt_of_payload_lt hpayload
  · unfold wholeCubeProgressRank
    omega

#print axioms wholeCubeProgressRank_lt_of_payload_lt
#print axioms wholeCubeProgressRank_lt_of_discovery
#print axioms wholeCubeProgressRank_lt_of_progress

end OrderedEdgeColoring
end JSP000404Research
