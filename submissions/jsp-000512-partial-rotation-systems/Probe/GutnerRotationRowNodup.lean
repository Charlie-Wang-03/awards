import Probe.GutnerRotationRows
import Mathlib.Tactic.FinCases

namespace JSP512Probe.Gutner

set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- Every typed cyclic neighbour row is duplicate-free.  Splitting on the
source vertex keeps each kernel computation small. -/
theorem neighborRow_nodup : ∀ u : Fin 86, (neighborRow u).Nodup := by
  intro u
  fin_cases u <;> decide +kernel

end JSP512Probe.Gutner
