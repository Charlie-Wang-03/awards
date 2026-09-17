import Probe.TriangularFaces

namespace JSP512Probe.RotationSystem
open CycleSurgery
variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj] (R : RotationSystem G)

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
/-- Local triangle closure determines the side opposite the center of a sector. -/
theorem sector_endpoints_of_closed (d : G.Dart)
    (hclose : R.face (R.face (R.face d.symm)) = d.symm) :
    (R.face (R.rotate d)).fst = (R.rotate d).snd ∧
      (R.face (R.rotate d)).snd = d.snd := by
  refine ⟨R.face_source _, ?_⟩
  have hfd : R.face d.symm = R.rotate d := by
    change R.rotate d.symm.symm = R.rotate d
    rw [SimpleGraph.Dart.symm_symm]
  rw [hfd] at hclose
  have hs := congrArg (fun x : G.Dart => x.fst) hclose
  rw [R.face_source] at hs
  exact hs

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
/-- The third side of the triangular sector between two consecutive outgoing darts. -/
theorem triangular_sector_endpoints (htri : ∀ d, R.face (R.face (R.face d)) = d)
    (d : G.Dart) :
    (R.face (R.rotate d)).fst = (R.rotate d).snd ∧
      (R.face (R.rotate d)).snd = d.snd :=
  R.sector_endpoints_of_closed d (htri d.symm)

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
/-- Triangle closure gives an actual edge between consecutive neighbors. -/
theorem triangular_neighbors_adj (htri : ∀ d, R.face (R.face (R.face d)) = d)
    (d : G.Dart) : G.Adj d.snd (R.rotate d).snd := by
  have h := (R.face (R.rotate d)).adj.symm
  rw [(R.triangular_sector_endpoints htri d).1,
    (R.triangular_sector_endpoints htri d).2] at h
  exact h

/-- Outgoing darts at a vertex correspond bijectively to its neighbors. -/
def neighborDartEquiv (v : V) : {d : G.Dart // d.fst = v} ≃ G.neighborSet v where
  toFun d := ⟨d.val.snd, by have h := d.val.adj; rwa [d.property] at h⟩
  invFun w := ⟨⟨(v,w.val),w.property⟩,rfl⟩
  left_inv d := by
    apply Subtype.ext
    exact SimpleGraph.Dart.ext _ _ (Prod.ext d.property.symm rfl)
  right_inv _ := rfl

def sourceRotation (v : V) : Equiv.Perm {d : G.Dart // d.fst = v} :=
  R.rotate.subtypeEquiv (fun d => by rw [R.source])

def neighborRotation (v : V) : Equiv.Perm (G.neighborSet v) :=
  (((neighborDartEquiv (G := G) v).symm).trans (R.sourceRotation v)).trans
    (neighborDartEquiv (G := G) v)

omit [DecidableEq V] in
/-- Every neighbor occurs in the single cyclic order inherited from the source rotation. -/
theorem neighborRotation_sameCycle (v : V) (x y : G.neighborSet v) :
    (R.neighborRotation v).SameCycle x y := by
  let e := neighborDartEquiv (G := G) v
  have h := transport_cycles e.symm (R.sourceRotation v) x y
  simp only [Equiv.symm_symm] at h
  apply h.mpr
  apply (subtype_cycles R.rotate _ (fun d => by rw [R.source]) _ _).mpr
  exact R.local_cycle _ _ ((e.symm x).property.trans (e.symm y).property.symm)

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
/-- Consecutive entries of the neighbor permutation are joined in the graph. -/
theorem neighborRotation_adj (htri : ∀ d, R.face (R.face (R.face d)) = d)
    (v : V) (x : G.neighborSet v) : G.Adj x.val ((R.neighborRotation v) x).val := by
  let d : G.Dart := ⟨(v,x.val),x.property⟩
  exact R.triangular_neighbors_adj htri d

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
/-- The cyclic neighbor order has no fixed points, including the two-neighbor case. -/
theorem neighborRotation_ne_self (htri : ∀ d, R.face (R.face (R.face d)) = d)
    (v : V) (x : G.neighborSet v) : R.neighborRotation v x ≠ x := by
  intro h
  have ha := R.neighborRotation_adj htri v x
  rw [h] at ha
  exact G.irrefl ha

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
/-- For a boundary fan, all but one neighbor transition is supplied by a
triangular sector; the exceptional transition is reserved for the outer face. -/
theorem neighborRotation_adj_except (v : V) (outer : G.Dart)
    (hfan : ∀ d : G.Dart, d.fst = v → d ≠ outer →
      R.face (R.face (R.face d.symm)) = d.symm)
    (x : G.neighborSet v) (hx : x.val ≠ outer.snd) :
    G.Adj x.val ((R.neighborRotation v) x).val := by
  let d : G.Dart := ⟨(v,x.val),x.property⟩
  have hd : d ≠ outer := fun h => hx (congrArg (fun d : G.Dart => d.snd) h)
  have hp := R.sector_endpoints_of_closed d (hfan d rfl hd)
  have ha := (R.face (R.rotate d)).adj.symm
  rw [hp.1,hp.2] at ha
  exact ha

end JSP512Probe.RotationSystem
