import Probe.GutnerFaceSetup

namespace JSP512Probe.Gutner

set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- A facial orbit is one of the listed exceptional orbits exactly when its
three-step return fails. All other facial orbits are triangles. -/
theorem mem_quadOrbits_iff_three_ne (d : graph.Dart) :
    Quotient.mk (Equiv.Perm.SameCycle.setoid rotationSystem.face) d ∈ quadOrbits ↔
      rotationSystem.face (rotationSystem.face (rotationSystem.face d)) ≠ d := by
  decide +kernel +revert

end JSP512Probe.Gutner
