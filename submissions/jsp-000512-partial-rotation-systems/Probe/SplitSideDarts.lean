import Probe.SplitFaceStructure
import Probe.SectorFanRoute

namespace JSP512Probe.RotationSystem
open EdgeInsertion
variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj] (R : RotationSystem G)
  (a b : G.Dart) (hab : a.fst = b.fst)

/-- An original dart whose refined source lies in a chosen component gives
an actual dart of the induced projected side, with unchanged old endpoints. -/
def splitSideDart (mark d : G.Dart)
    (hd : (RefinedRotation.graph G (R.splitRotation a b) (R.split_source a b hab)).Reachable
      (RefinedRotation.vertex G (R.splitRotation a b) d)
      (RefinedRotation.vertex G (R.splitRotation a b) mark)) :
    (G.induce (R.splitSide a b hab mark)).Dart := by
  let H := RefinedRotation.graph G (R.splitRotation a b) (R.split_source a b hab)
  let q := RefinedRotation.vertex G (R.splitRotation a b)
  have hs : H.Reachable (q d.symm) (q mark) :=
    (show H.Adj (q d) (q d.symm) from ⟨d, rfl, rfl⟩).reachable.symm.trans hd
  exact ⟨(⟨d.fst, ⟨d, rfl, hd⟩⟩, ⟨d.snd, ⟨d.symm, rfl, hs⟩⟩), d.adj⟩

/-- A side facial step away from the two split destinations agrees with the
original facial step, in the actual transported rotation. -/
theorem splitSideDart_face (hne : a ≠ b) (hc : G.Preconnected)
    (hz : R.HasGenusZero) (hf : R.face.SameCycle a b) (mark d e : G.Dart)
    (hd : (RefinedRotation.graph G (R.splitRotation a b) (R.split_source a b hab)).Reachable
      (RefinedRotation.vertex G (R.splitRotation a b) d)
      (RefinedRotation.vertex G (R.splitRotation a b) mark))
    (he : (RefinedRotation.graph G (R.splitRotation a b) (R.split_source a b hab)).Reachable
      (RefinedRotation.vertex G (R.splitRotation a b) e)
      (RefinedRotation.vertex G (R.splitRotation a b) mark))
    (hstep : R.face d = e) (hea : e ≠ a) (heb : e ≠ b) :
    (R.splitSideRotation a b hab hne hc hz hf mark).face (R.splitSideDart a b hab mark d hd) =
      R.splitSideDart a b hab mark e he := by
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
  change ((S.componentRotation C).mapIso iso).face (isoDarts iso xd) = isoDarts iso xe
  rw [(S.componentRotation C).mapIso_face iso xd]
  apply congrArg (isoDarts iso)
  apply F.injective
  apply Subtype.ext
  change ((closedDartEquiv C.supp hclosed) ((S.restrictClosed C.supp hclosed).face xd)).val =
    ((closedDartEquiv C.supp hclosed) xe).val
  rw [S.restrictClosed_face C.supp hclosed xd]
  change S.face (E d) = E e
  rw [RefinedRotation.face_dart]
  change E (Equiv.swap a b (R.face d)) = E e
  rw [hstep, Equiv.swap_apply_of_ne_of_ne hea heb]

/-- A facial path avoiding the two cut destinations stays in the component
of its initial dart; membership need only be established at the start. -/
theorem split_path_in_component (mark : G.Dart) (n : ℕ) (d : Fin (n+1) → G.Dart)
    (h0 : (RefinedRotation.graph G (R.splitRotation a b) (R.split_source a b hab)).Reachable
      (RefinedRotation.vertex G (R.splitRotation a b) (d 0))
      (RefinedRotation.vertex G (R.splitRotation a b) mark))
    (hstep : ∀ i : Fin n, R.face (d i.castSucc) = d i.succ)
    (ha : ∀ i : Fin n, d i.succ ≠ a) (hb : ∀ i : Fin n, d i.succ ≠ b) :
    ∀ i, (RefinedRotation.graph G (R.splitRotation a b) (R.split_source a b hab)).Reachable
      (RefinedRotation.vertex G (R.splitRotation a b) (d i))
      (RefinedRotation.vertex G (R.splitRotation a b) mark) := by
  let H := RefinedRotation.graph G (R.splitRotation a b) (R.split_source a b hab)
  let S := RefinedRotation.rotation G (R.splitRotation a b) (R.split_source a b hab)
  let E := RefinedRotation.dartEquiv G (R.splitRotation a b) (R.split_source a b hab)
  have step : ∀ i : Fin n, H.Reachable (E (d i.succ)).fst (E (d i.castSucc)).fst := by
    intro i
    have he : S.face (E (d i.castSucc)) = E (d i.succ) := by
      rw [RefinedRotation.face_dart]
      change E (Equiv.swap a b (R.face (d i.castSucc))) = E (d i.succ)
      rw [hstep, Equiv.swap_apply_of_ne_of_ne (ha i) (hb i)]
    have hv : (E (d i.castSucc)).snd = (E (d i.succ)).fst := by
      rw [← he, S.face_source]
    have hr := (E (d i.castSucc)).adj.reachable
    rw [hv] at hr
    exact hr.symm
  intro i
  induction i using Fin.induction with
  | zero => exact h0
  | succ i ih => exact (step i).trans ih

/-- An original finite route staying in a split component and not crossing
its two cut destinations becomes a route of the actual induced-side rotation. -/
theorem splitSideDart_route (hne : a ≠ b) (hc : G.Preconnected)
    (hz : R.HasGenusZero) (hf : R.face.SameCycle a b) (mark : G.Dart)
    (n : ℕ) (d : Fin (n+1) → G.Dart)
    (hd : ∀ i, (RefinedRotation.graph G (R.splitRotation a b) (R.split_source a b hab)).Reachable
      (RefinedRotation.vertex G (R.splitRotation a b) (d i))
      (RefinedRotation.vertex G (R.splitRotation a b) mark))
    (hstep : ∀ i : Fin n, R.face (d i.castSucc) = d i.succ)
    (ha : ∀ i : Fin n, d i.succ ≠ a) (hb : ∀ i : Fin n, d i.succ ≠ b) :
    let f := fun i => R.splitSideDart a b hab mark (d i) (hd i)
    FaceRoute (R.splitSideRotation a b hab hne hc hz hf mark).face (f 0)
      (List.ofFn (fun i : Fin n => f i.succ)) := by
  dsimp only
  apply FaceRoute.of_steps _ n (fun i => R.splitSideDart a b hab mark (d i) (hd i))
  intro i
  exact R.splitSideDart_face a b hab hne hc hz hf mark _ _ _ _ (hstep i) (ha i) (hb i)

/-- From one component-membership proof and distinct original targets, a
cut-avoiding path yields the initialized fan route on the actual induced side. -/
theorem splitSideDart_start_route (hne : a ≠ b) (hc : G.Preconnected)
    (hz : R.HasGenusZero) (hf : R.face.SameCycle a b) (mark : G.Dart)
    (n : ℕ) (d : Fin (n+1) → G.Dart)
    (h0 : (RefinedRotation.graph G (R.splitRotation a b) (R.split_source a b hab)).Reachable
      (RefinedRotation.vertex G (R.splitRotation a b) (d 0))
      (RefinedRotation.vertex G (R.splitRotation a b) mark))
    (hstep : ∀ i : Fin n, R.face (d i.castSucc) = d i.succ)
    (ha : ∀ i : Fin n, d i.succ ≠ a) (hb : ∀ i : Fin n, d i.succ ≠ b)
    (htarget : Function.Injective (fun i => (d i).snd)) :
    letI : Fintype (R.splitSide a b hab mark) := Fintype.ofFinite _
    let hd := R.split_path_in_component a b hab mark n d h0 hstep ha hb
    let f := fun i => R.splitSideDart a b hab mark (d i) (hd i)
    let H := G.induce (R.splitSide a b hab mark)
    let S := R.splitSideRotation a b hab hne hc hz hf mark
    let anchor := (f 0).symm
    FanRoute (fanStartGraph H anchor) (startFan H S anchor) (startAnchor H anchor)
      ((List.ofFn (fun i : Fin n => f i.succ)).map (startOldDart H anchor)) := by
  classical
  let : Fintype (R.splitSide a b hab mark) := Fintype.ofFinite _
  dsimp only
  apply startFan_route
  · exact R.splitSideDart_route a b hab hne hc hz hf mark n d _ hstep ha hb
  · apply List.pairwise_ofFn.mpr
    intro i j hij he
    have hh := htarget (congrArg Subtype.val he)
    have heq : i = j := by simpa using hh
    exact (ne_of_lt hij) heq
  · intro x hx he
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hx
    have hh := htarget (congrArg Subtype.val he)
    have hv := congrArg Fin.val hh
    simp at hv

end JSP512Probe.RotationSystem
