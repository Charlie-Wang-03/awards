import Probe.SplitSideDarts

namespace JSP512Probe.RotationSystem
open EdgeInsertion
variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj] (R : RotationSystem G)
  (a b : G.Dart) (hab : a.fst = b.fst)

/-- Include the first path dart by attaching the center to its source, rather
than its target. This retains the endpoint spoke needed at a chord. -/
theorem splitSideDart_full_start_route (hne : a ≠ b) (hc : G.Preconnected)
    (hz : R.HasGenusZero) (hf : R.face.SameCycle a b) (mark : G.Dart)
    (n : ℕ) (d : Fin (n+1) → G.Dart)
    (h0 : (RefinedRotation.graph G (R.splitRotation a b) (R.split_source a b hab)).Reachable
      (RefinedRotation.vertex G (R.splitRotation a b) (d 0))
      (RefinedRotation.vertex G (R.splitRotation a b) mark))
    (hstep : ∀ i : Fin n, R.face (d i.castSucc) = d i.succ)
    (ha : ∀ i : Fin n, d i.succ ≠ a) (hb : ∀ i : Fin n, d i.succ ≠ b)
    (htarget : Function.Injective (fun i => (d i).snd))
    (havoid : ∀ i, (d i).snd ≠ (d 0).fst) :
    letI : Fintype (R.splitSide a b hab mark) := Fintype.ofFinite _
    let hd := R.split_path_in_component a b hab mark n d h0 hstep ha hb
    let f := fun i => R.splitSideDart a b hab mark (d i) (hd i)
    let H := G.induce (R.splitSide a b hab mark)
    let S := R.splitSideRotation a b hab hne hc hz hf mark
    let anchor := (S.face.symm (f 0)).symm
    FanRoute (fanStartGraph H anchor) (startFan H S anchor) (startAnchor H anchor)
      ((List.ofFn f).map (startOldDart H anchor)) := by
  classical
  let : Fintype (R.splitSide a b hab mark) := Fintype.ofFinite _
  let hd := R.split_path_in_component a b hab mark n d h0 hstep ha hb
  let f := fun i => R.splitSideDart a b hab mark (d i) (hd i)
  let S := R.splitSideRotation a b hab hne hc hz hf mark
  dsimp only
  apply startFan_route
  · change FaceRoute S.face (S.face.symm (f 0)) (List.ofFn f)
    rw [List.ofFn_succ]
    exact ⟨S.face.apply_symm_apply _,
      R.splitSideDart_route a b hab hne hc hz hf mark n d hd hstep ha hb⟩
  · apply List.pairwise_ofFn.mpr
    intro i j hij he
    exact (ne_of_lt hij) (htarget (congrArg Subtype.val he))
  · intro x hx he
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hx
    apply havoid i
    have hh : (f i).snd = (S.face.symm (f 0)).snd := he
    rw [S.face_inverse_target] at hh
    exact congrArg Subtype.val hh

end JSP512Probe.RotationSystem
