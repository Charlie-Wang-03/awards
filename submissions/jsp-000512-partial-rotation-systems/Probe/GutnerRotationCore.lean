import Probe.GutnerRotationPermutation
import Probe.RotationSystem

namespace JSP512Probe.Gutner

set_option maxRecDepth 100000
set_option maxHeartbeats 0

instance rotationSameCycleDecidable : DecidableRel (Equiv.Perm.SameCycle rotationPerm) :=
  Equiv.Perm.instDecidableRelSameCycle rotationPerm

/-- Each source fibre is exactly one rotation cycle. -/
theorem rotation_local_cycle : ∀ d e : graph.Dart, d.fst = e.fst →
    Equiv.Perm.SameCycle rotationPerm d e := by
  decide +kernel

/-- A rotation system for the explicit 86-vertex Gutner graph. -/
def rotationSystem : RotationSystem graph where
  rotate := rotationPerm
  source := by intro d; rfl
  local_cycle := rotation_local_cycle

end JSP512Probe.Gutner
