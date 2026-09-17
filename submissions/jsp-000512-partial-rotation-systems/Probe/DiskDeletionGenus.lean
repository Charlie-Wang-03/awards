import Probe.OuterDartCount
import Probe.VertexDeletionGenus

namespace JSP512Probe.RotationSystem
variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj] (R : RotationSystem G)

/-- Deleting a boundary vertex preserves zero genus for the actual rotation,
even when boundary chords make the new outer traversal repeat vertices. -/
theorem boundary_deleteVertex_genusZero (outer : G.Dart) (hz : R.HasGenusZero)
    (hc : G.Preconnected)
    (hsimple : ∀ a b, R.face.SameCycle outer a → R.face.SameCycle outer b →
      a.fst = b.fst → a = b)
    (hinner : ∀ a, ¬R.face.SameCycle outer a → R.face (R.face (R.face a)) = a)
    (hcorner : R.face outer ≠ outer.symm) :
    (R.deleteVertex outer.snd).HasGenusZero := by
  classical
  have hn := R.nonbacktracking_corner_card outer hcorner
  have : Nontrivial V := Fintype.one_lt_card_iff_nontrivial.mp (by omega)
  let W := {u : V | u ≠ outer.snd}
  let H := VertexDeletedGraph (G := G) outer.snd
  have hv := vertex_deleted_vertex_count (V := V) outer.snd
  have : Nontrivial W := Fintype.one_lt_card_iff_nontrivial.mp (by
    change 1 < Fintype.card {u : V | u ≠ outer.snd}
    omega)
  have hc' : H.Connected := R.outer_vertex_deleted_connected outer hc hsimple hinner
  have hconn : G.Connected := ⟨hc⟩
  have hs := hc.support_eq_univ
  have hs' := hc'.preconnected.support_eq_univ
  have hsup : supportSize (G := G) = (Fintype.card V : ℤ) := by
    simp only [supportSize, hs, Nat.card_eq_fintype_card, Fintype.card_setUniv]
  have hsup' : supportSize (G := H) = (Fintype.card W : ℤ) := by
    simp only [supportSize, hs', Nat.card_eq_fintype_card, Fintype.card_setUniv]
    exact congrArg (fun n : ℕ => (n : ℤ)) (Fintype.card_congr (Equiv.refl _))
  have hcomp := component_card_of_connected G hconn
  have hcomp' := component_card_of_connected H hc'
  obtain ⟨root,hr⟩ := R.outer_region_single_orbit outer hsimple hinner hcorner
  have htri : ∀ x, ¬(R.deleteVertex outer.snd).face.SameCycle root x →
      (R.deleteVertex outer.snd).face ((R.deleteVertex outer.snd).face
        ((R.deleteVertex outer.snd).face x)) = x := by
    intro x hx
    exact R.outside_outer_region_triangular outer hinner x (fun h => hx ((hr x).mpr h))
  have hl := R.outer_deleted_dart_length outer hsimple hinner root hr
  have hf := R.disk_face_count outer hinner
  have hf' := (R.deleteVertex outer.snd).disk_face_count root htri
  have he := vertex_deleted_edge_count (G := G) outer.snd
  change R.eulerDefect = 0 at hz
  unfold eulerDefect at hz
  rw [hsup, hcomp] at hz
  change (R.deleteVertex outer.snd).eulerDefect = 0
  unfold eulerDefect
  change 2 * (Nat.card H.ConnectedComponent : ℤ) - 2 * Fintype.card W +
    supportSize (G := H) + Nat.card H.edgeSet - (R.deleteVertex outer.snd).faceCount = 0
  rw [hsup', hcomp']
  change Fintype.card W + 1 = Fintype.card V at hv
  change Nat.card H.edgeSet + G.degree outer.snd = Nat.card G.edgeSet at he
  change 3 * (R.deleteVertex outer.snd).faceCount +
    (R.deleteVertex outer.snd).faceLength root = 2 * Nat.card H.edgeSet + 3 at hf'
  omega
/-- The chordless specialization used by disk/list reduction. -/
theorem disk_deleteVertex_genusZero (outer : G.Dart) (hz : R.HasGenusZero)
    (hc : G.Preconnected)
    (hsimple : ∀ a b, R.face.SameCycle outer a → R.face.SameCycle outer b →
      a.fst = b.fst → a = b)
    (hinner : ∀ a, ¬R.face.SameCycle outer a → R.face (R.face (R.face a)) = a)
    (hcorner : R.face outer ≠ outer.symm)
    (_hchord : ∀ a, R.face.SameCycle outer a → G.Adj outer.snd a.fst →
      a.fst = outer.fst ∨ a.fst = (R.face outer).snd) :
    (R.deleteVertex outer.snd).HasGenusZero := by
  exact R.boundary_deleteVertex_genusZero outer hz hc hsimple hinner hcorner
end JSP512Probe.RotationSystem
