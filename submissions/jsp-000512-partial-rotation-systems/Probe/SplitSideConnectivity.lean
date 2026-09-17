import Probe.RestoreSeparator

namespace JSP512Probe.RefinedRotation
variable {V : Type*} [Fintype V] [DecidableEq V]
  (G : SimpleGraph V) [DecidableRel G.Adj] (σ : Equiv.Perm G.Dart)
  (hs : ∀ d, (σ d).fst = d.fst)

/-- Forgetting split copies maps every actual refined edge to its original edge. -/
def projectHom : graph G σ hs →g G where
  toFun := project G σ hs
  map_rel' := by
    rintro x y ⟨d,hd,he⟩
    have h := d.adj
    change G.Adj (project G σ hs (vertex G σ d)) (project G σ hs (vertex G σ d.symm)) at h
    rwa [hd,he] at h
end JSP512Probe.RefinedRotation

namespace JSP512Probe.RotationSystem
variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj] (R : RotationSystem G)
  (a b : G.Dart) (hab : a.fst = b.fst)

/-- Every projected split component induces a connected graph on old vertices. -/
theorem splitSide_connected (mark : G.Dart) : (G.induce (R.splitSide a b hab mark)).Connected := by
  classical
  let σ := R.splitRotation a b
  let H := RefinedRotation.graph G σ (R.split_source a b hab)
  let q := RefinedRotation.vertex G σ
  let project := RefinedRotation.project G σ (R.split_source a b hab)
  let C := H.connectedComponentMk (q mark)
  have mem : ∀ z : C, project z.val ∈ R.splitSide a b hab mark := by
    rintro ⟨z,hz⟩
    induction z using Quotient.inductionOn with
    | h d =>
      refine ⟨d,rfl,?_⟩
      exact SimpleGraph.ConnectedComponent.eq.mp hz
  let j : C.toSimpleGraph →g G.induce (R.splitSide a b hab mark) :=
    ⟨fun z => ⟨project z.val,mem z⟩,fun h =>
      (RefinedRotation.projectHom G σ (R.split_source a b hab)).map_adj h⟩
  have surj : Function.Surjective j := by
    intro u
    obtain ⟨d,hd,hr⟩ := u.property
    have hm : q d ∈ C.supp := SimpleGraph.ConnectedComponent.eq.mpr hr
    exact ⟨⟨q d,hm⟩,Subtype.ext hd⟩
  exact C.connected_toSimpleGraph.map j surj

/-- Projection is injective within a component: only the two separated copies
can share an old vertex, and they cannot belong to the same component. -/
theorem split_project_injective_on_component (hne : a ≠ b) (hc : G.Preconnected)
    (hz : R.HasGenusZero) (hf : R.face.SameCycle a b)
    (d e : G.Dart) (hde : d.fst = e.fst)
    (hr : (RefinedRotation.graph G (R.splitRotation a b) (R.split_source a b hab)).Reachable
      (RefinedRotation.vertex G (R.splitRotation a b) d)
      (RefinedRotation.vertex G (R.splitRotation a b) e)) :
    RefinedRotation.vertex G (R.splitRotation a b) d =
      RefinedRotation.vertex G (R.splitRotation a b) e := by
  let q := RefinedRotation.vertex G (R.splitRotation a b)
  change (RefinedRotation.graph G (R.splitRotation a b) (R.split_source a b hab)).Reachable (q d) (q e) at hr
  by_cases hd : d.fst = a.fst
  · have he := hde.symm.trans hd
    rcases R.split_cycles_at a b hab hne d hd with hda | hdb <;>
      rcases R.split_cycles_at a b hab hne e he with hea | heb
    · exact (Quotient.sound hda).trans (Quotient.sound hea).symm
    · have hda' : q d = q a := Quotient.sound hda
      have heb' : q e = q b := Quotient.sound heb
      rw [hda',heb'] at hr
      exact False.elim (R.split_copies_not_reachable a b hab hne hc hz hf hr)
    · have hdb' : q d = q b := Quotient.sound hdb
      have hea' : q e = q a := Quotient.sound hea
      rw [hdb',hea'] at hr
      exact False.elim (R.split_copies_not_reachable a b hab hne hc hz hf hr.symm)
    · exact (Quotient.sound hdb).trans (Quotient.sound heb).symm
  · exact Quotient.sound (R.split_cycles_away a b hab hne d e hd hde)

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
/-- Adding the deleted vertex to a connected survivor side containing one of
its neighbors preserves connectedness. -/
theorem restoreSide_connected (v : V) (A : Set {u : V | u ≠ v})
    (hc : ((VertexDeletedGraph (G := G) v).induce A).Connected)
    (w : {u : V | u ≠ v}) (hw : w ∈ A) (hvw : G.Adj v w.val) :
    (G.induce (restoreSide v A)).Connected := by
  let K := G.induce (restoreSide v A)
  let j : (VertexDeletedGraph (G := G) v).induce A →g K :=
    ⟨fun z => ⟨z.val.val,(survivor_mem_restoreSide v A z.val).mpr z.property⟩,fun h => h⟩
  let anchor : restoreSide v A := ⟨w.val,(survivor_mem_restoreSide v A w).mpr hw⟩
  let center : restoreSide v A := ⟨v,Or.inl rfl⟩
  have allreach : ∀ x : restoreSide v A, K.Reachable x anchor := by
    rintro ⟨x,hx⟩
    rcases hx with he | ⟨z,hz,he⟩
    · subst x
      exact (show K.Adj center anchor from hvw).reachable
    · subst x
      exact (hc.preconnected ⟨z,hz⟩ ⟨w,hw⟩).map j
  have : Nonempty (restoreSide v A) := ⟨center⟩
  exact ⟨fun x y => (allreach x).trans (allreach y).symm⟩
/-- The two restored induced chord sides are connected and strictly smaller,
with full edge coverage and intersection exactly the chord endpoints. -/
theorem chord_connected_separator (outer : G.Dart) (hz : R.HasGenusZero) (hc : G.Preconnected)
    (hsimple : ∀ a b, R.face.SameCycle outer a → R.face.SameCycle outer b → a.fst = b.fst → a = b)
    (hinner : ∀ a, ¬R.face.SameCycle outer a → R.face (R.face (R.face a)) = a)
    (hcorner : R.face outer ≠ outer.symm)
    (ch : G.Dart) (ha : R.face.SameCycle outer ch) (hadj : G.Adj outer.snd ch.fst)
    (hleft : ch.fst ≠ outer.fst) (hright : ch.fst ≠ (R.face outer).snd) :
    ∃ A B : Set V, (G.induce A).Connected ∧ (G.induce B).Connected ∧
      (∀ u, u ∈ A ∨ u ∈ B) ∧
      (∀ u z, G.Adj u z → (u ∈ A ∧ z ∈ A) ∨ (u ∈ B ∧ z ∈ B)) ∧
      (∀ u, (u ∈ A ∧ u ∈ B) ↔ u = outer.snd ∨ u = ch.fst) ∧
      Nat.card A < Fintype.card V ∧ Nat.card B < Fintype.card V := by
  classical
  obtain ⟨root,hr⟩ := R.outer_region_single_orbit outer hsimple hinner hcorner
  obtain ⟨x,y,hx,hy,hne,hxy,hu⟩ :=
    R.chord_exposes_repeated_vertex outer hsimple hinner root hr ch ha hadj hleft hright
  let S := R.deleteVertex outer.snd
  have hs := R.boundary_deleteVertex_genusZero outer hz hc hsimple hinner hcorner
  have hconn := R.outer_vertex_deleted_connected outer hc hsimple hinner
  let A := S.splitSide x y hxy x
  let B := S.splitSide x y hxy y
  have hf := hx.symm.trans hy
  have hp := S.split_sides_proper x y hxy hne hconn.preconnected hs hf
  have result := restore_separator (G := G) outer.snd A B x.fst
    (S.split_sides_cover x y hxy hne hconn.preconnected)
    (S.split_sides_edges x y hxy hne hconn.preconnected)
    (S.split_sides_inter x y hxy hne hconn.preconnected hs hf)
    ⟨y.snd,hp.2.2⟩ ⟨x.snd,hp.1.2⟩
  have hw := (S.split_sides_inter x y hxy hne hconn.preconnected hs hf x.fst).mpr rfl
  have hadj' : G.Adj outer.snd x.fst.val := hu ▸ hadj
  refine ⟨restoreSide outer.snd A,restoreSide outer.snd B,
    restoreSide_connected outer.snd A (S.splitSide_connected x y hxy x) x.fst hw.1 hadj',
    restoreSide_connected outer.snd B (S.splitSide_connected x y hxy y) x.fst hw.2 hadj',?_⟩
  simpa only [hu] using result

end JSP512Probe.RotationSystem
