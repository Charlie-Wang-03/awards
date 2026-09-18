import Probe.GutnerFaceSetup

namespace JSP512Probe.Gutner

set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- Every concrete vertex is reachable from the shared root vertex 0.
Each vertex is either adjacent to 0 directly, or adjacent to the other shared
root 1, which itself is adjacent to 0. -/
theorem reachable_from_root (x : Fin 86) : graph.Reachable 0 x := by
  have h01 : graph.Reachable (0 : Fin 86) 1 :=
    SimpleGraph.Adj.reachable (by decide)
  fin_cases x <;>
    first
    | exact SimpleGraph.Adj.reachable (by decide)
    | exact h01.trans (SimpleGraph.Adj.reachable (by decide))

/-- The concrete obstruction graph is connected. -/
theorem graph_connected : graph.Connected := by
  rw [SimpleGraph.connected_iff_exists_forall_reachable]
  exact ⟨0, reachable_from_root⟩

end JSP512Probe.Gutner
