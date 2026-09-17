import Probe.GutnerRotationRows
import Mathlib.Tactic.FinCases

namespace JSP512Probe.Gutner

set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- Every local cyclic neighbour row has at least two elements. -/
theorem neighborRow_nontrivial : ∀ u : Fin 86, 2 ≤ (neighborRow u).length := by
  intro u
  fin_cases u <;> decide +kernel

end JSP512Probe.Gutner
