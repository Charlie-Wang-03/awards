import Probe.SplitSideDartTransport

namespace JSP512Probe.RotationSystem
variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj] (R : RotationSystem G)
  (a b : G.Dart) (hab : a.fst = b.fst)
  (hne : a ≠ b) (hc : G.Preconnected) (hz : R.HasGenusZero) (hf : R.face.SameCycle a b)

include hne hc hz hf in
/-- Old outer darts in the same refined component lie on the same split
outer face. This identifies a path-selected root with that component's outer. -/
theorem split_outer_same_component (d e : G.Dart)
    (hd : R.face.SameCycle a d) (he : R.face.SameCycle a e)
    (hr : (RefinedRotation.graph G (R.splitRotation a b) (R.split_source a b hab)).Reachable
      (RefinedRotation.vertex G (R.splitRotation a b) d)
      (RefinedRotation.vertex G (R.splitRotation a b) e)) :
    (Equiv.swap a b * R.face).SameCycle d e := by
  classical
  let H := RefinedRotation.graph G (R.splitRotation a b) (R.split_source a b hab)
  let S := RefinedRotation.rotation G (R.splitRotation a b) (R.split_source a b hab)
  let E := RefinedRotation.dartEquiv G (R.splitRotation a b) (R.split_source a b hab)
  have reach : ∀ u v, (Equiv.swap a b * R.face).SameCycle u v →
      H.Reachable (E u).fst (E v).fst := by
    intro u v huv
    exact EdgeInsertion.face_reachable H S (E u) (E v)
      ((R.split_face_cycles a b hab u v).mpr huv)
  have hsep := R.split_copies_not_reachable a b hab hne hc hz hf
  rcases (CycleSurgery.split_cycle_partition R.face a b d hne hf).mp hd.symm with hda | hdb
  · rcases (CycleSurgery.split_cycle_partition R.face a b e hne hf).mp he.symm with hea | heb
    · exact hda.trans hea.symm
    · exact False.elim (hsep ((reach d a hda).symm.trans (hr.trans (reach e b heb))))
  · rcases (CycleSurgery.split_cycle_partition R.face a b e hne hf).mp he.symm with hea | heb
    · exact False.elim (hsep ((reach e a hea).symm.trans (hr.symm.trans (reach d b hdb))))
    · exact hdb.trans heb.symm

/-- An original inner triangle remains triangular in the actual induced side. -/
theorem splitSideDart_triangle (mark d : G.Dart) (hd)
    (ho : ¬R.face.SameCycle a d) (ht : R.face (R.face (R.face d)) = d) :
    let T := R.splitSideRotation a b hab hne hc hz hf mark
    let z := R.splitSideDart a b hab mark d hd
    T.face (T.face (T.face z)) = z := by
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
  change ((S.componentRotation C).mapIso iso).face
    (((S.componentRotation C).mapIso iso).face
      (((S.componentRotation C).mapIso iso).face (isoDarts iso xd))) = isoDarts iso xd
  apply (S.componentRotation C).mapIso_triangle iso xd
  apply S.restrictClosed_triangle C.supp hclosed xd
  exact R.split_preserves_inner_triangle a b hab hf d ho ht

/-- All faces other than the precise outer root selected by a restoration
path are triangular in the actual induced-side rotation. -/
theorem splitSideDart_inner_at (mark root : G.Dart) (hr)
    (hroot : R.face.SameCycle a root)
    (hi : ∀ d, ¬R.face.SameCycle a d → R.face (R.face (R.face d)) = d) :
    let T := R.splitSideRotation a b hab hne hc hz hf mark
    let r := R.splitSideDart a b hab mark root hr
    ∀ z, ¬T.face.SameCycle r z → T.face (T.face (T.face z)) = z := by
  dsimp only
  intro z hn
  obtain ⟨d,hd,rfl⟩ := R.splitSideDart_surjective a b hab hne hc hz hf mark z
  have ho : ¬R.face.SameCycle a d := by
    intro hod
    apply hn
    apply (R.splitSideDart_face_cycles a b hab hne hc hz hf mark root d hr hd).mpr
    exact R.split_outer_same_component a b hab hne hc hz hf root d hroot hod (hr.trans hd.symm)
  exact R.splitSideDart_triangle a b hab hne hc hz hf mark d hd ho (hi d ho)

/-- The precise inverse-face anchor used for full fan restoration has the
same inner-triangle guarantee as its path-selected root. -/
theorem splitSideDart_anchor_inner (mark root : G.Dart) (hr)
    (hroot : R.face.SameCycle a root)
    (hi : ∀ d, ¬R.face.SameCycle a d → R.face (R.face (R.face d)) = d) :
    let T := R.splitSideRotation a b hab hne hc hz hf mark
    let r := R.splitSideDart a b hab mark root hr
    let anchor := (T.face.symm r).symm
    ∀ z, ¬T.face.SameCycle anchor.symm z → T.face (T.face (T.face z)) = z := by
  dsimp only
  intro z hn
  apply R.splitSideDart_inner_at a b hab hne hc hz hf mark root hr hroot hi z
  intro hh
  exact hn (by simpa only [SimpleGraph.Dart.symm_symm] using hh.symm_apply_left)

end JSP512Probe.RotationSystem
