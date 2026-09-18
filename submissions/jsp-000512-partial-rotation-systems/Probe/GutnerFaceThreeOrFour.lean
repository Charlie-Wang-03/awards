import Probe.GutnerFaceSetup

namespace JSP512Probe.Gutner

set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- Every face has length three or four. -/
theorem face_three_or_four (d : graph.Dart) :
    rotationSystem.face (rotationSystem.face (rotationSystem.face d)) = d ∨
    rotationSystem.face (rotationSystem.face (rotationSystem.face (rotationSystem.face d))) = d := by
  decide +kernel +revert

end JSP512Probe.Gutner
