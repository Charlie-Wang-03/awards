import Probe.GutnerFaceSetup
import Probe.GutnerRotationRowNodup
import Probe.GutnerRotationRowExhaustive
import Mathlib.Combinatorics.SimpleGraph.DegreeSum

namespace JSP512Probe.Gutner

set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- The explicit cyclic row contains every neighbour exactly once, so its
length is the graph degree at that vertex. -/
theorem neighborRow_length_eq_degree (u : Fin 86) :
    (neighborRow u).length = graph.degree u := by
  rw [← SimpleGraph.card_neighborSet_eq_degree]
  rw [← Finset.card_univ]
  rw [← List.toFinset_card_of_nodup (neighborRow_nodup u)]
  congr 1
  ext x
  simp [neighborRow_exhaustive]

/-- The sum of the 86 explicit neighbour-row lengths is 482. -/
theorem neighborRow_length_sum :
    ∑ u : Fin 86, (neighborRow u).length = 482 := by
  decide +kernel

/-- Its edge table has exactly 241 undirected edges. -/
theorem graph_edgeFinset_card : graph.edgeFinset.card = 241 := by
  have hsum : ∑ u : Fin 86, graph.degree u = 482 := by
    calc
      ∑ u : Fin 86, graph.degree u =
          ∑ u : Fin 86, (neighborRow u).length := by
            apply Finset.sum_congr rfl
            intro u hu
            exact (neighborRow_length_eq_degree u).symm
      _ = 482 := neighborRow_length_sum
  have hhand := graph.sum_degrees_eq_twice_card_edges
  omega

end JSP512Probe.Gutner
