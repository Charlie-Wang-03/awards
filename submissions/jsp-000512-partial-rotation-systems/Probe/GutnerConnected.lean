import Probe.GutnerFaceSetup
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Finite

namespace JSP512Probe.Gutner

set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- The concrete obstruction graph is connected. -/
theorem graph_connected : graph.Connected := by
  decide +kernel

end JSP512Probe.Gutner
