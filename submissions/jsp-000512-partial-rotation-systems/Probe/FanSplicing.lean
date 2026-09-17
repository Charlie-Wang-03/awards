import Probe.VertexDeletion

namespace JSP512Probe.RotationSystem
variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj] (R : RotationSystem G) (v : V)

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
/-- The side opposite the center of a triangular sector survives center deletion. -/
theorem sector_survives (d : G.Dart) (hd : d.fst = v)
    (hclose : R.face (R.face (R.face d.symm)) = d.symm) :
    (R.face (R.rotate d)).fst ≠ v ∧ (R.face (R.rotate d)).snd ≠ v := by
  have hp := R.sector_endpoints_of_closed d hclose
  rw [hp.1,hp.2]
  constructor
  · have hs : (R.rotate d).fst = v := (R.source d).trans hd
    rw [← hs]
    exact (R.rotate d).snd_ne_fst
  · rw [← hd]
    exact d.snd_ne_fst

/-- The actual surviving dart forming the opposite side of a triangular sector. -/
def sectorDeletedDart (d : G.Dart) (hd : d.fst = v)
    (hclose : R.face (R.face (R.face d.symm)) = d.symm) :
    (VertexDeletedGraph (G := G) v).Dart :=
  (vertexDeletedDartEquiv v).symm ⟨R.face (R.rotate d),R.sector_survives v d hd hclose⟩

/-- After center deletion, the sector side follows the old outgoing dart's face step. -/
theorem sector_deleted_face (d : G.Dart) (hd : d.fst = v)
    (hclose : R.face (R.face (R.face d.symm)) = d.symm) :
    ((vertexDeletedDartEquiv v)
      ((R.deleteVertex v).face (R.sectorDeletedDart v d hd hclose))).val = R.face d := by
  rw [R.vertex_deleted_face_formula]
  change (if (R.face (R.face (R.rotate d))).snd = v then
    R.rotate (R.face (R.face (R.rotate d))) else R.face (R.face (R.rotate d))) = R.face d
  have hfd : R.face d.symm = R.rotate d := by
    change R.rotate d.symm.symm = R.rotate d
    rw [SimpleGraph.Dart.symm_symm]
  rw [hfd] at hclose
  rw [hclose]
  have ht : d.symm.snd = v := hd
  rw [ite_eq_left ht]
  rfl

/-- Consecutive triangular sectors splice in the reverse source-rotation order. -/
theorem sector_predecessor_step (d e : G.Dart) (hd : d.fst = v) (he : e.fst = v)
    (hpred : R.rotate e = d)
    (hclosed : R.face (R.face (R.face d.symm)) = d.symm)
    (hclosee : R.face (R.face (R.face e.symm)) = e.symm) :
    (R.deleteVertex v).face (R.sectorDeletedDart v d hd hclosed) =
      R.sectorDeletedDart v e he hclosee := by
  apply (vertexDeletedDartEquiv v).injective
  apply Subtype.ext
  rw [R.sector_deleted_face]
  change R.face d = R.face (R.rotate e)
  rw [hpred]

/-- Any facial step whose two endpoint darts survive is unchanged. -/
theorem deleted_face_step_of_survives (x y : (VertexDeletedGraph (G := G) v).Dart)
    (hstep : R.face ((vertexDeletedDartEquiv v) x).val =
      ((vertexDeletedDartEquiv v) y).val) : (R.deleteVertex v).face x = y := by
  apply (vertexDeletedDartEquiv v).injective
  apply Subtype.ext
  rw [R.vertex_deleted_face_formula, hstep,
    ite_eq_right ((vertexDeletedDartEquiv v) y).property.2]

/-- A triangular face all of whose darts survive remains triangular after deletion. -/
theorem deleted_triangle_preserved (x y z : (VertexDeletedGraph (G := G) v).Dart)
    (hxy : R.face ((vertexDeletedDartEquiv v) x).val = ((vertexDeletedDartEquiv v) y).val)
    (hyz : R.face ((vertexDeletedDartEquiv v) y).val = ((vertexDeletedDartEquiv v) z).val)
    (hzx : R.face ((vertexDeletedDartEquiv v) z).val = ((vertexDeletedDartEquiv v) x).val) :
    (R.deleteVertex v).face ((R.deleteVertex v).face ((R.deleteVertex v).face x)) = x := by
  rw [R.deleted_face_step_of_survives v x y hxy,
    R.deleted_face_step_of_survives v y z hyz, R.deleted_face_step_of_survives v z x hzx]

end JSP512Probe.RotationSystem
