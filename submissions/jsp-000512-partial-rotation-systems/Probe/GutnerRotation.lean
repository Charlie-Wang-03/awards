import Probe.GutnerFaceQuadCard
import Probe.GutnerFaceThreeNe
import Probe.GutnerFaceThreeOrFour
import Probe.GutnerFaceTwoNe
import Probe.GutnerEdgeCard
import Probe.GutnerConnected

namespace JSP512Probe.Gutner

open RotationSystem CycleSurgery

set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- Structured orbit counting: 146 triangular faces and eleven quadrilateral
faces give 157 facial orbits without enumerating quotient equality pairwise. -/
theorem faceOrbit_card : Fintype.card FaceOrbit = 157 := by
  classical
  have hsize : ∀ q : FaceOrbit, orbitSize rotationSystem.face q =
      if q ∈ quadOrbits then 4 else 3 := by
    intro q
    induction q using Quotient.inductionOn with
    | h d =>
      by_cases hq : Quotient.mk (Equiv.Perm.SameCycle.setoid rotationSystem.face) d ∈ quadOrbits
      · rw [if_pos hq]
        apply orbitSize_eq_four rotationSystem.face d
        · exact rotationSystem.face_ne_self d
        · exact face_two_ne d
        · exact (mem_quadOrbits_iff_three_ne d).mp hq
        · exact (face_three_or_four d).resolve_left ((mem_quadOrbits_iff_three_ne d).mp hq)
      · rw [if_neg hq]
        apply orbitSize_eq_three rotationSystem.face d (rotationSystem.face_ne_self d)
        by_contra hne
        exact hq ((mem_quadOrbits_iff_three_ne d).mpr hne)
  have hsum := sum_orbitSize rotationSystem.face
  have hrewrite :
      (∑ q : FaceOrbit, orbitSize rotationSystem.face q) =
      ∑ q : FaceOrbit, (if q ∈ quadOrbits then 4 else 3) := by
    apply Finset.sum_congr rfl
    intro q _
    exact hsize q
  rw [hrewrite] at hsum
  have heval :
      (∑ q : FaceOrbit, (if q ∈ quadOrbits then 4 else 3)) =
      3 * Fintype.card FaceOrbit + quadOrbits.card := by
    calc
      (∑ q : FaceOrbit, (if q ∈ quadOrbits then 4 else 3)) =
          ∑ q : FaceOrbit, (3 + if q ∈ quadOrbits then 1 else 0) := by
            apply Finset.sum_congr rfl
            intro q _
            by_cases hq : q ∈ quadOrbits <;> simp [hq]
      _ = 3 * Fintype.card FaceOrbit + quadOrbits.card := by
        simp [Finset.sum_add_distrib, Nat.mul_comm]
  rw [heval, quadOrbits_card] at hsum
  rw [SimpleGraph.dart_card_eq_twice_card_edges] at hsum
  rw [graph_edgeFinset_card] at hsum
  omega


theorem faceCount_eq : rotationSystem.faceCount = 157 := by
  unfold RotationSystem.faceCount RotationSystem.FaceOrbit
  rw [Nat.card_eq_fintype_card]
  exact faceOrbit_card

/-- Its edge table has exactly 241 undirected edges. -/
theorem graph_edge_count : Nat.card graph.edgeSet = 241 := by
  simpa only [SimpleGraph.edgeFinset, Set.toFinset_card] using graph_edgeFinset_card

noncomputable def componentEquivUnit : graph.ConnectedComponent ≃ Unit where
  toFun := fun _ => ()
  invFun := fun _ => graph.connectedComponentMk 0
  left_inv := by
    intro q
    induction q using Quotient.inductionOn with
    | h v =>
      apply Quotient.sound
      exact graph_connected 0 v
  right_inv := by intro u; cases u; rfl


theorem component_count : Nat.card graph.ConnectedComponent = 1 := by
  simpa using Nat.card_congr componentEquivUnit

/-- The finite rotation table satisfies the spherical Euler equation, hence
is genus zero in the exact sense used by the coloring development. -/
theorem rotation_genusZero : rotationSystem.HasGenusZero := by
  have hs : supportSize (G := graph) = 86 := by
    unfold supportSize
    rw [graph_connected.preconnected.support_eq_univ]
    simp
  unfold HasGenusZero eulerDefect
  rw [component_count, hs, graph_edge_count, faceCount_eq]
  norm_num

end JSP512Probe.Gutner
