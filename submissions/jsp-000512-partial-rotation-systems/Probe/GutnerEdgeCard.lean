import Probe.GutnerFaceSetup

namespace JSP512Probe.Gutner

set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- Its edge table has exactly 241 undirected edges. -/
theorem graph_edgeFinset_card : graph.edgeFinset.card = 241 := by
  decide +kernel

end JSP512Probe.Gutner
