import Probe.DeletionFaceCounting
import Probe.TriangularFaces
import Mathlib.Combinatorics.SimpleGraph.DeleteEdges

namespace JSP512Probe.RotationSystem
variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj] (R : RotationSystem G)

/-- Removing a vertex removes exactly its degree many edges. -/
theorem vertex_deleted_edge_count (v : V) :
    Nat.card (VertexDeletedGraph (G := G) v).edgeSet + G.degree v =
      Nat.card G.edgeSet := by
  classical
  have hh := G.card_edgeFinset_induce_compl_singleton v
  rw [G.card_edgeFinset_deleteIncidenceSet] at hh
  have hd := G.degree_le_card_edgeFinset v
  have he : (VertexDeletedGraph (G := G) v).edgeFinset.card =
      (G.induce {v}ᶜ).edgeFinset.card := rfl
  rw [← he] at hh
  simp only [SimpleGraph.edgeFinset_card, ← Nat.card_eq_fintype_card] at hh hd
  omega

/-- The surviving vertex carrier loses exactly one element. -/
theorem vertex_deleted_vertex_count (v : V) :
    Fintype.card {u : V | u ≠ v} + 1 = Fintype.card V := by
  classical
  have hh := Fintype.card_subtype_compl (fun u : V => u = v)
  have hp : 0 < Fintype.card V := Fintype.card_pos_iff.mpr ⟨v⟩
  simp only [Fintype.card_unique] at hh
  have he : Fintype.card {u : V | u ≠ v} = Fintype.card {u : V // ¬u = v} :=
    Fintype.card_congr (Equiv.refl _)
  rw [he]
  omega

/-- The actual sourcewise vertex deletion preserves genus zero for a maximal
triangular rotation with at least three vertices. -/
theorem maximal_deleteVertex_genusZero (hz : R.HasGenusZero)
    (hmax : EdgeMaximalGenusZero G) (hn : 3 ≤ Fintype.card V) (v : V) :
    (R.deleteVertex v).HasGenusZero := by
  classical
  have : Nontrivial V := Fintype.one_lt_card_iff_nontrivial.mp (by omega)
  let W := {u : V | u ≠ v}
  let H := VertexDeletedGraph (G := G) v
  have hv := vertex_deleted_vertex_count (V := V) v
  have : Nontrivial W := Fintype.one_lt_card_iff_nontrivial.mp (by change 1 < Fintype.card {u : V | u ≠ v}; omega)
  have hc := R.maximal_connected hz hmax
  have hc' : H.Connected := R.maximal_vertex_deleted_connected hz hmax v
  have hs := hc.preconnected.support_eq_univ
  have hs' := hc'.preconnected.support_eq_univ
  have hsup : supportSize (G := G) = (Fintype.card V : ℤ) := by
    simp only [supportSize, hs, Nat.card_eq_fintype_card, Fintype.card_setUniv]
  have hsup' : supportSize (G := H) = (Fintype.card W : ℤ) := by
    simp only [supportSize, hs', Nat.card_eq_fintype_card, Fintype.card_setUniv]
    exact congrArg (fun n : ℕ => (n : ℤ)) (Fintype.card_congr (Equiv.refl _))
  have hcomp := component_card_of_connected G hc
  have hcomp' := component_card_of_connected H hc'
  have hmem : v ∈ G.support := by rw [hs]; trivial
  obtain ⟨u, hu⟩ := G.mem_support.mp hmem
  let root : {d : G.Dart // d.fst = v} := ⟨⟨(v,u),hu⟩,rfl⟩
  have ht := R.maximal_face_three_steps hz hmax hn
  have hf := R.triangular_face_count ht
  have hf' := R.deleted_face_count v ht root
  have he := vertex_deleted_edge_count (G := G) v
  change R.eulerDefect = 0 at hz
  unfold eulerDefect at hz
  rw [hsup, hcomp] at hz
  change (R.deleteVertex v).eulerDefect = 0
  unfold eulerDefect
  change 2 * (Nat.card H.ConnectedComponent : ℤ) - 2 * Fintype.card W +
    supportSize (G := H) + Nat.card H.edgeSet - (R.deleteVertex v).faceCount = 0
  rw [hsup', hcomp']
  change Fintype.card W + 1 = Fintype.card V at hv
  change Nat.card H.edgeSet + G.degree v = Nat.card G.edgeSet at he
  change 3 * (R.deleteVertex v).faceCount + G.degree v = 2 * Nat.card H.edgeSet + 3 at hf'
  omega
end JSP512Probe.RotationSystem
