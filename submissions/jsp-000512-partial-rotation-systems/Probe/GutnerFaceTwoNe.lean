import Probe.GutnerFaceSetup

namespace JSP512Probe.Gutner

set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- No facial orbit has length one or two. -/
theorem face_two_ne (d : graph.Dart) :
    rotationSystem.face (rotationSystem.face d) ≠ d := by
  decide +kernel

end JSP512Probe.Gutner
