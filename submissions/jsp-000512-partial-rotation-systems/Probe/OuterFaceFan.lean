import Probe.FanSplicing

namespace JSP512Probe.RotationSystem
open CycleSurgery
variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj] (R : RotationSystem G)

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
/-- At a simple outer face, exactly one sector at an incident vertex can be
outer; every other sector inherits inner triangular closure. -/
theorem outer_face_fan (outer : G.Dart)
    (hsimple : ∀ x y, R.face.SameCycle outer x → R.face.SameCycle outer y →
      x.fst = y.fst → x = y)
    (hinner : ∀ x, ¬R.face.SameCycle outer x → R.face (R.face (R.face x)) = x)
    (d : G.Dart) (hd : d.fst = outer.snd) (hne : d ≠ outer.symm) :
    R.face (R.face (R.face d.symm)) = d.symm := by
  apply hinner
  intro hc
  have he : R.face d.symm = R.face outer := hsimple _ _ hc.apply_right
    Equiv.Perm.SameCycle.rfl.apply_right (by rw [R.face_source, R.face_source]; exact hd)
  have hh := R.face.injective he
  apply hne
  simpa only [SimpleGraph.Dart.symm_symm] using congrArg SimpleGraph.Dart.symm hh

/-- A triangular fan with one possible outer sector connects all neighbors:
the missing transition breaks a cycle into a path, not into separate components. -/
theorem fan_neighbor_preconnected (v : V) (outer : G.Dart) (ho : outer.fst = v)
    (hfan : ∀ d : G.Dart, d.fst = v → d ≠ outer →
      R.face (R.face (R.face d.symm)) = d.symm) :
    (G.induce (G.neighborSet v)).Preconnected := by
  let H := G.induce (G.neighborSet v)
  let σ := R.neighborRotation v
  let last : G.neighborSet v := ⟨outer.snd, by change G.Adj v outer.snd; rw [← ho]; exact outer.adj⟩
  have reach : ∀ n : ℕ, ∀ x, (σ ^ n) x = last → H.Reachable x last := by
    intro n
    induction n with
    | zero =>
      intro x hx
      have he : x = last := hx
      rw [he]
    | succ n ih =>
      intro x hx
      by_cases he : x = last
      · rw [he]
      · have hv : x.val ≠ outer.snd := fun h => he (Subtype.ext h)
        have ha : H.Adj x (σ x) := R.neighborRotation_adj_except v outer hfan x hv
        apply ha.reachable.trans
        apply ih (σ x)
        simpa only [pow_succ, Equiv.Perm.mul_apply] using hx
  have allreach : ∀ x, H.Reachable x last := by
    intro x
    obtain ⟨n, hn⟩ := (R.neighborRotation_sameCycle v x last).exists_nat_pow_eq
    exact reach n x hn
  intro x y
  exact (allreach x).trans (allreach y).symm

omit [Fintype V] [DecidableRel G.Adj] in
/-- Neighbor connectivity lets every passage through the deleted vertex be
rerouted inside its surviving neighbor graph. -/
theorem vertex_deleted_preconnected_of_neighbors (v : V) (hc : G.Preconnected)
    (hl : (G.induce (G.neighborSet v)).Preconnected) :
    (VertexDeletedGraph (G := G) v).Preconnected := by
  classical
  intro x y
  have hv : v ∈ G.support :=
    SimpleGraph.mem_support_of_reachable x.property.symm (hc v x.val)
  obtain ⟨w, hw⟩ := G.mem_support.mp hv
  let H := VertexDeletedGraph (G := G) v
  let j : G.induce (G.neighborSet v) →g H :=
    ⟨fun z => ⟨z.val, z.property.ne.symm⟩, fun h => h⟩
  let f (z : V) : {z | z ≠ v} := if h : z = v then ⟨w,hw.ne.symm⟩ else ⟨z,h⟩
  have neighbors : ∀ (z : V) (h : G.Adj v z), H.Reachable (f v) (f z) := by
    intro z h
    have hr := (hl ⟨w,hw⟩ ⟨z,h⟩).map j
    change H.Reachable ⟨w,hw.ne.symm⟩ ⟨z,h.ne.symm⟩ at hr
    simpa only [f, dite_eq_left rfl, dite_eq_right h.ne.symm] using hr
  have step : ∀ a b, G.Adj a b → H.Reachable (f a) (f b) := by
    intro a b h
    by_cases ha : a = v
    · subst a
      exact neighbors b h
    · by_cases hb : b = v
      · subst b
        exact (neighbors a h.symm).symm
      · apply SimpleGraph.Adj.reachable
        change G.Adj (f a).val (f b).val
        simpa only [f, dite_eq_right ha, dite_eq_right hb] using h
  have transport : ∀ {a b}, G.Walk a b → H.Reachable (f a) (f b) := by
    intro a b p
    induction p with
    | nil => exact SimpleGraph.Reachable.rfl
    | cons h _ ih => exact (step _ _ h).trans ih
  obtain ⟨p⟩ := hc x.val y.val
  have hr := transport p
  simpa only [f, dite_eq_right x.property, dite_eq_right y.property] using hr

/-- Deleting a boundary vertex of a connected rotation with a simple outer
face and triangular inner faces leaves a connected induced graph. -/
theorem outer_vertex_deleted_connected (outer : G.Dart) (hc : G.Preconnected)
    (hsimple : ∀ x y, R.face.SameCycle outer x → R.face.SameCycle outer y →
      x.fst = y.fst → x = y)
    (hinner : ∀ x, ¬R.face.SameCycle outer x → R.face (R.face (R.face x)) = x) :
    (VertexDeletedGraph (G := G) outer.snd).Connected := by
  have hl := R.fan_neighbor_preconnected outer.snd outer.symm rfl
    (R.outer_face_fan outer hsimple hinner)
  have : Nonempty {z : V | z ≠ outer.snd} := ⟨⟨outer.fst,outer.adj.ne⟩⟩
  exact ⟨vertex_deleted_preconnected_of_neighbors outer.snd hc hl⟩

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
/-- The opposite side of an inner sector cannot belong to the old outer face. -/
theorem inner_sector_not_outer (outer d : G.Dart)
    (hinner : ¬R.face.SameCycle outer d.symm) :
    ¬R.face.SameCycle outer (R.face (R.rotate d)) := by
  intro hc
  apply hinner
  have hh := hc.of_apply_right
  have he : R.rotate d = R.face d.symm := by
    change R.rotate d = R.rotate d.symm.symm
    rw [SimpleGraph.Dart.symm_symm]
  rw [he] at hh
  exact hh.of_apply_right

/-- At the incoming end of the removed outer corner, the surviving outer
walk enters the last triangular sector in the vertex rotation. -/
theorem outer_splice_entry (outer e : G.Dart)
    (he : e.fst = outer.snd) (hpred : R.rotate e = outer.symm)
    (hclose : R.face (R.face (R.face e.symm)) = e.symm)
    (x : (VertexDeletedGraph (G := G) outer.snd).Dart)
    (hx : R.face ((vertexDeletedDartEquiv outer.snd) x).val = outer) :
    (R.deleteVertex outer.snd).face x = R.sectorDeletedDart outer.snd e he hclose := by
  apply (vertexDeletedDartEquiv outer.snd).injective
  apply Subtype.ext
  rw [R.vertex_deleted_face_formula, hx, ite_eq_left rfl]
  change R.rotate outer = R.face (R.rotate e)
  rw [hpred]
  change R.rotate outer = R.rotate outer.symm.symm
  rw [SimpleGraph.Dart.symm_symm]

/-- At the outgoing end of the removed outer corner, the first triangular
sector rejoins the surviving old outer walk. -/
theorem outer_splice_exit (outer : G.Dart)
    (hclose : R.face (R.face (R.face (R.face outer).symm)) = (R.face outer).symm)
    (y : (VertexDeletedGraph (G := G) outer.snd).Dart)
    (hy : ((vertexDeletedDartEquiv outer.snd) y).val = R.face (R.face outer)) :
    (R.deleteVertex outer.snd).face
      (R.sectorDeletedDart outer.snd (R.face outer) (R.face_source outer) hclose) = y := by
  apply (vertexDeletedDartEquiv outer.snd).injective
  apply Subtype.ext
  rw [R.sector_deleted_face, hy]

end JSP512Probe.RotationSystem
