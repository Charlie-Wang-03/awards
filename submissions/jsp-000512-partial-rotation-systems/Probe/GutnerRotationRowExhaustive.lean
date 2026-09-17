import Probe.GutnerRotationRows
import Mathlib.Tactic.FinCases

namespace JSP512Probe.Gutner

set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- Every graph edge is present in the explicit raw rotation row at its source.
Use the adjacency witness carried by `graph.Adj`, so verification does not have
to rediscover the existential block witness for every possible neighbour. -/
theorem rotationRows_mem_of_adj {u v : Fin 86} (h : graph.Adj u v) :
    v ∈ rotationRows u := by
  rcases h with ⟨_, i, a, b, he, hxy⟩
  rcases hxy with hxy | hxy
  · rcases hxy with ⟨rfl, rfl⟩
    fin_cases a <;> fin_cases b <;> simp_all [blockEdges]
    all_goals fin_cases i <;> decide +kernel
  · rcases hxy with ⟨rfl, rfl⟩
    fin_cases a <;> fin_cases b <;> simp_all [blockEdges]
    all_goals fin_cases i <;> decide +kernel

/-- Every actual neighbour occurs in the corresponding typed cyclic row. -/
theorem neighborRow_exhaustive :
    ∀ (u : Fin 86) (x : graph.neighborSet u), x ∈ neighborRow u := by
  intro u x
  unfold neighborRow
  rw [List.mem_filterMap]
  refine ⟨(x : Fin 86), rotationRows_mem_of_adj x.property, ?_⟩
  simp [x.property]

end JSP512Probe.Gutner
