import Probe.GutnerFaceSetup

namespace JSP512Probe.Gutner

set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- The eleven listed roots represent eleven distinct face orbits. -/
theorem quadOrbits_card : quadOrbits.card = 11 := by
  decide +kernel

end JSP512Probe.Gutner
