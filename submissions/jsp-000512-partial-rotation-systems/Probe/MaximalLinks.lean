import Probe.MaximalNoBridges

namespace JSP512Probe.RotationSystem
variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj] (R : RotationSystem G)

/-- Distinct consecutive neighbors in a vertex rotation are adjacent. -/
theorem maximal_consecutive_neighbors_adj (hz : R.HasGenusZero)
    (hmax : EdgeMaximalGenusZero G) (d : G.Dart) (hn : R.rotate d ≠ d) :
    G.Adj d.snd (R.rotate d).snd := by
  have hne : d.snd ≠ (R.rotate d).snd := by
    intro h
    exact hn (SimpleGraph.Dart.ext _ _ (Prod.ext (R.source d) h.symm))
  have hf : R.face.SameCycle d.symm (R.face (R.rotate d)) := by
    have hh : R.face d.symm = R.rotate d := by
      change R.rotate d.symm.symm = R.rotate d
      rw [SimpleGraph.Dart.symm_symm]
    rw [← hh]
    exact Equiv.Perm.SameCycle.rfl.apply_right.apply_right
  have ha := R.maximal_face_vertices_adj hz hmax d.symm
    (R.face (R.rotate d)) (by rw [R.face_source]; exact hne) hf
  rw [R.face_source] at ha
  exact ha

/-- The neighbors of a vertex form a preconnected induced graph. In particular,
paths between neighbors can avoid the vertex itself. -/
theorem maximal_neighbor_preconnected (hz : R.HasGenusZero)
    (hmax : EdgeMaximalGenusZero G) (v : V) :
    (G.induce (G.neighborSet v)).Preconnected := by
  intro x y
  let d : G.Dart := ⟨(v,x.val),x.property⟩
  let e : G.Dart := ⟨(v,y.val),y.property⟩
  have hc : R.rotate.SameCycle d e := R.local_cycle d e rfl
  obtain ⟨n, hn⟩ := hc.exists_nat_pow_eq
  have hs : ∀ k : ℕ, ((R.rotate ^ k) d).fst = v := by
    intro k
    exact (R.sameCycle_iff_source _ _).mp
      (Equiv.Perm.SameCycle.rfl.pow_right) |>.symm
  let endpoint (k : ℕ) : G.neighborSet v :=
    ⟨((R.rotate ^ k) d).snd, by
      have h := ((R.rotate ^ k) d).adj
      rwa [hs k] at h⟩
  have hr : ∀ k, (G.induce (G.neighborSet v)).Reachable x (endpoint k) := by
    intro k
    induction k with
    | zero => exact SimpleGraph.Reachable.rfl
    | succ k ih =>
      let z := (R.rotate ^ k) d
      by_cases hf : R.rotate z = z
      · have he : endpoint (k+1) = endpoint k := by
          apply Subtype.ext
          change ((R.rotate ^ (k+1)) d).snd = ((R.rotate ^ k) d).snd
          rw [pow_succ', Equiv.Perm.mul_apply]
          exact congrArg (fun a : G.Dart => a.snd) hf
        rw [he]
        exact ih
      · have ha := R.maximal_consecutive_neighbors_adj hz hmax z hf
        apply ih.trans
        apply SimpleGraph.Adj.reachable
        change G.Adj ((R.rotate ^ k) d).snd ((R.rotate ^ (k+1)) d).snd
        simpa only [pow_succ', Equiv.Perm.mul_apply] using ha
  have he : endpoint n = y := by
    apply Subtype.ext
    exact congrArg (fun a : G.Dart => a.snd) hn
  simpa only [he] using hr n

/-- Removing any one vertex preserves pairwise reachability among the survivors. -/
theorem maximal_vertex_deleted_preconnected (hz : R.HasGenusZero)
    (hmax : EdgeMaximalGenusZero G) (v : V) :
    (G.induce {z | z ≠ v}).Preconnected := by
  classical
  intro x y
  have hc := R.maximal_preconnected hz hmax
  have hv : v ∈ G.support :=
    SimpleGraph.mem_support_of_reachable x.property.symm (hc v x.val)
  obtain ⟨w, hw⟩ := G.mem_support.mp hv
  let H := G.induce {z | z ≠ v}
  let j : G.induce (G.neighborSet v) →g H :=
    ⟨fun z => ⟨z.val, z.property.ne.symm⟩, fun h => h⟩
  let f (z : V) : {z | z ≠ v} := if h : z = v then ⟨w,hw.ne.symm⟩ else ⟨z,h⟩
  have neighbors : ∀ (z : V) (h : G.Adj v z), H.Reachable (f v) (f z) := by
    intro z h
    have hr := (R.maximal_neighbor_preconnected hz hmax v ⟨w,hw⟩ ⟨z,h⟩).map j
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

/-- On a nontrivial vertex type, each one-vertex deletion is connected. -/
theorem maximal_vertex_deleted_connected [Nontrivial V] (hz : R.HasGenusZero)
    (hmax : EdgeMaximalGenusZero G) (v : V) :
    (G.induce {z | z ≠ v}).Connected := by
  obtain ⟨w,hw⟩ := exists_ne v
  have : Nonempty {z : V | z ≠ v} := ⟨⟨w,hw⟩⟩
  exact ⟨R.maximal_vertex_deleted_preconnected hz hmax v⟩

end JSP512Probe.RotationSystem
