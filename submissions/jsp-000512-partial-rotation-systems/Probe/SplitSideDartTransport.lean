import Probe.SplitSideDarts

namespace JSP512Probe.RotationSystem
variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj] (R : RotationSystem G)
  (a b : G.Dart) (hab : a.fst = b.fst)

/-- Every dart of an actual induced side comes from an original dart whose
refined source lies in that side's component. -/
theorem splitSideDart_surjective (hne : a ≠ b) (hc : G.Preconnected)
    (hz : R.HasGenusZero) (hf : R.face.SameCycle a b) (mark : G.Dart)
    (z : (G.induce (R.splitSide a b hab mark)).Dart) :
    ∃ (d : G.Dart) (hd :
      (RefinedRotation.graph G (R.splitRotation a b) (R.split_source a b hab)).Reachable
        (RefinedRotation.vertex G (R.splitRotation a b) d)
        (RefinedRotation.vertex G (R.splitRotation a b) mark)),
      R.splitSideDart a b hab mark d hd = z := by
  let H := RefinedRotation.graph G (R.splitRotation a b) (R.split_source a b hab)
  let q := RefinedRotation.vertex G (R.splitRotation a b)
  let p := RefinedRotation.project G (R.splitRotation a b) (R.split_source a b hab)
  obtain ⟨u,hu,hru⟩ := z.fst.property
  obtain ⟨v,hv,hrv⟩ := z.snd.property
  have ha : G.Adj u.fst v.fst := by rw [hu,hv]; exact z.adj
  obtain ⟨d,hd,hds⟩ := R.split_project_reflects_adj a b hab hne hc hz hf u v
    (hru.trans hrv.symm) ha
  have hdr : H.Reachable (q d) (q mark) := by
    change H.Reachable (q u) (q mark) at hru
    change q d = q u at hd
    rw [hd]
    exact hru
  refine ⟨d,hdr,?_⟩
  apply SimpleGraph.Dart.ext
  apply Prod.ext
  · apply Subtype.ext
    exact (congrArg p hd).trans hu
  · apply Subtype.ext
    exact (congrArg p hds).trans hv

/-- Equality of transported side darts reflects equality of their old darts. -/
theorem splitSideDart_injective (mark d e : G.Dart) (hd he)
    (h : R.splitSideDart a b hab mark d hd = R.splitSideDart a b hab mark e he) : d = e := by
  apply SimpleGraph.Dart.ext
  apply Prod.ext
  · exact congrArg (fun z => z.fst.val) h
  · exact congrArg (fun z => z.snd.val) h

/-- Actual induced-side facial orbits are precisely the corresponding split
facial orbits of old darts, including steps at the two cut destinations. -/
theorem splitSideDart_face_cycles (hne : a ≠ b) (hc : G.Preconnected)
    (hz : R.HasGenusZero) (hf : R.face.SameCycle a b) (mark d e : G.Dart) (hd he) :
    (R.splitSideRotation a b hab hne hc hz hf mark).face.SameCycle
      (R.splitSideDart a b hab mark d hd) (R.splitSideDart a b hab mark e he) ↔
      (Equiv.swap a b * R.face).SameCycle d e := by
  classical
  let σ := R.splitRotation a b
  let : Fintype (RefinedRotation.Vertex G σ) := Fintype.ofFinite _
  let H := RefinedRotation.graph G σ (R.split_source a b hab)
  let S := RefinedRotation.rotation G σ (R.split_source a b hab)
  let E := RefinedRotation.dartEquiv G σ (R.split_source a b hab)
  let C := H.connectedComponentMk (RefinedRotation.vertex G σ mark)
  let : Fintype C := Fintype.ofFinite _
  let : Fintype (R.splitSide a b hab mark) := Fintype.ofFinite _
  let hclosed := fun u (hu : u ∈ C.supp) v (huv : H.Adj u v) =>
    C.mem_supp_of_adj_mem_supp hu huv
  let F := closedDartEquiv C.supp hclosed
  let iso := R.split_component_iso a b hab hne hc hz hf mark
  let xd := F.symm ⟨E d, SimpleGraph.ConnectedComponent.eq.mpr hd⟩
  let xe := F.symm ⟨E e, SimpleGraph.ConnectedComponent.eq.mpr he⟩
  change ((S.componentRotation C).mapIso iso).face.SameCycle
    (isoDarts iso xd) (isoDarts iso xe) ↔ _
  rw [(S.componentRotation C).mapIso_face_cycles iso xd xe]
  change (S.restrictClosed C.supp hclosed).face.SameCycle xd xe ↔ _
  rw [S.restrictClosed_face_cycles C.supp hclosed xd xe]
  change S.face.SameCycle (E d) (E e) ↔ _
  exact R.split_face_cycles a b hab d e

/-- A side outer-face dart lifts to the original outer face whenever the
chosen side root lifts there. This covers arbitrary side darts, not only the
sector path used to construct a restoration route. -/
theorem splitSideDart_outer_lift (hne : a ≠ b) (hc : G.Preconnected)
    (hz : R.HasGenusZero) (hf : R.face.SameCycle a b)
    (mark root : G.Dart) (hr)
    (hroot : R.face.SameCycle a root)
    (z : (G.induce (R.splitSide a b hab mark)).Dart)
    (hzface : (R.splitSideRotation a b hab hne hc hz hf mark).face.SameCycle
      (R.splitSideDart a b hab mark root hr) z) :
    ∃ (d : G.Dart) (hd :
      (RefinedRotation.graph G (R.splitRotation a b) (R.split_source a b hab)).Reachable
        (RefinedRotation.vertex G (R.splitRotation a b) d)
        (RefinedRotation.vertex G (R.splitRotation a b) mark)),
      R.splitSideDart a b hab mark d hd = z ∧ R.face.SameCycle a d := by
  obtain ⟨d,hd,rfl⟩ := R.splitSideDart_surjective a b hab hne hc hz hf mark z
  refine ⟨d,hd,rfl,?_⟩
  have hrd := (R.splitSideDart_face_cycles a b hab hne hc hz hf mark root d hr hd).mp hzface
  apply Equiv.Perm.SameCycle.symm
  apply (CycleSurgery.split_cycle_partition R.face a b d hne hf).mpr
  rcases (CycleSurgery.split_cycle_partition R.face a b root hne hf).mp hroot.symm with h | h
  · exact Or.inl (hrd.symm.trans h)
  · exact Or.inr (hrd.symm.trans h)

end JSP512Probe.RotationSystem
