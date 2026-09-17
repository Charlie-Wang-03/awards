import Probe.GutnerRotationRows
import Mathlib.Tactic.FinCases

namespace JSP512Probe.Gutner

set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- Every actual neighbour occurs in the corresponding typed cyclic row.
Splitting on the source vertex prevents one monolithic finite reduction. -/
theorem neighborRow_exhaustive :
    ∀ (u : Fin 86) (x : graph.neighborSet u), x ∈ neighborRow u := by
  intro u
  fin_cases u <;> decide +kernel

end JSP512Probe.Gutner
