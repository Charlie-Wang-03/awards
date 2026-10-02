import JSP000404Research.ResidualWholeCubeUnifiedRank
import Mathlib.Order.WellFounded
import Mathlib.Tactic

/-!
# Well-founded relation for genuine whole-cube recursion progress

The numerical rank

  4*payload + discoveryRank

turns every non-contractible whole-cube recursion step into strict descent.
This file packages that descent as an explicit WellFounded relation.

Exact T/Q repeats and exact T/T full rematches are intentionally absent from
this relation: they are contractions in the quotient state space, not genuine
recursive steps.
-/

namespace JSP000404Research
namespace OrderedEdgeColoring

structure WholeCubeProgressState (n : ℕ) where
  payload : ℕ
  discovered : Finset (Fin n)

def WholeCubeProgressState.rank
    {n : ℕ}
    (s : WholeCubeProgressState n) : ℕ :=
  wholeCubeProgressRank s.payload s.discovered

def WholeCubeProgressRel
    {n : ℕ}
    (next current : WholeCubeProgressState n) : Prop :=
  next.rank < current.rank

theorem wholeCubeProgressRel_wellFounded
    {n : ℕ} :
    WellFounded (@WholeCubeProgressRel n) := by
  exact (measure
    (fun s : WholeCubeProgressState n => s.rank)).wf

theorem wholeCubeProgressRel_of_payload_lt
    {n : ℕ}
    {current next : WholeCubeProgressState n}
    (hpayload : next.payload < current.payload) :
    WholeCubeProgressRel next current := by
  unfold WholeCubeProgressRel WholeCubeProgressState.rank
  exact wholeCubeProgressRank_lt_of_payload_lt hpayload

theorem wholeCubeProgressRel_of_new_coordinate
    {n : ℕ}
    {payload : ℕ}
    {coords : Finset (Fin n)}
    {d : Fin n}
    (hprogress :
      wholeCubeDiscoveryRank (insert d coords) <
        wholeCubeDiscoveryRank coords) :
    WholeCubeProgressRel
      ⟨payload,insert d coords⟩
      ⟨payload,coords⟩ := by
  unfold WholeCubeProgressRel WholeCubeProgressState.rank
  exact wholeCubeProgressRank_lt_of_discovery hprogress

#print axioms wholeCubeProgressRel_wellFounded
#print axioms wholeCubeProgressRel_of_payload_lt
#print axioms wholeCubeProgressRel_of_new_coordinate

end OrderedEdgeColoring
end JSP000404Research
