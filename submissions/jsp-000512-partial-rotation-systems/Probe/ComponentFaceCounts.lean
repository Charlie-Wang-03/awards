import Probe.ComponentCounts

namespace JSP512Probe.RotationSystem
variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj] (R : RotationSystem G)

/-- A face has the connected-component label of any of its sources. -/
def faceComponent : R.FaceOrbit → G.ConnectedComponent :=
  Quotient.lift (fun d : G.Dart => G.connectedComponentMk d.fst) (by
    intro d e h
    have hh := R.face_cycle_in_closed (G.connectedComponentMk d.fst).supp
      (fun _ hu _ huv => (G.connectedComponentMk d.fst).mem_supp_of_adj_mem_supp hu huv)
      d e rfl h
    exact hh.symm)

/-- Include a face of a component into the original face quotient. -/
noncomputable def componentFaceMap (C : G.ConnectedComponent) : (R.componentRotation C).FaceOrbit → R.FaceOrbit :=
  Quotient.map (fun x => ((closedDartEquiv C.supp
    (fun _ hu _ huv => C.mem_supp_of_adj_mem_supp hu huv)) x).val)
    (fun _ _ h => (R.restrictClosed_face_cycles C.supp
      (fun _ hu _ huv => C.mem_supp_of_adj_mem_supp hu huv) _ _).mp h)

omit [DecidableEq V] in
theorem faceComponent_map (C : G.ConnectedComponent) (q : (R.componentRotation C).FaceOrbit) :
    R.faceComponent (R.componentFaceMap C q) = C := by
  induction q using Quotient.inductionOn with
  | h x => exact x.fst.property

/-- Component faces partition all faces, bijectively and without any empty faces. -/
noncomputable def componentFacesEquiv :
    (Σ C : G.ConnectedComponent, (R.componentRotation C).FaceOrbit) ≃ R.FaceOrbit := by
  let f := fun q : Σ C : G.ConnectedComponent, (R.componentRotation C).FaceOrbit =>
    R.componentFaceMap q.1 q.2
  have hi : Function.Injective f := by
    rintro ⟨C,x⟩ ⟨D,y⟩ h
    have hCD : C = D := by
      have hh := congrArg R.faceComponent h
      change R.faceComponent (R.componentFaceMap C x) = R.faceComponent (R.componentFaceMap D y) at hh
      simpa only [R.faceComponent_map] using hh
    subst D
    suffices x = y by subst y; rfl
    induction x using Quotient.inductionOn with
    | h x =>
      induction y using Quotient.inductionOn with
      | h y =>
        apply Quotient.sound
        apply (R.restrictClosed_face_cycles C.supp
          (fun _ hu _ huv => C.mem_supp_of_adj_mem_supp hu huv) x y).mpr
        exact Quotient.exact h
  have hs : Function.Surjective f := by
    intro q
    induction q using Quotient.inductionOn with
    | h d =>
      let C := G.connectedComponentMk d.fst
      let e := closedDartEquiv C.supp (fun _ hu _ huv => C.mem_supp_of_adj_mem_supp hu huv)
      let x := e.symm ⟨d,rfl⟩
      refine ⟨⟨C,Quotient.mk _ x⟩,?_⟩
      change Quotient.mk _ (e x).val = Quotient.mk _ d
      rw [Equiv.apply_symm_apply]
  exact Equiv.ofBijective f ⟨hi,hs⟩

omit [DecidableEq V] in
/-- The original face count is the sum of actual restricted component face counts. -/
theorem sum_component_faces [Fintype G.ConnectedComponent] :
    ∑ C : G.ConnectedComponent, (R.componentRotation C).faceCount = R.faceCount := by
  classical
  let : ∀ C : G.ConnectedComponent, Fintype (R.componentRotation C).FaceOrbit :=
    fun _ => Fintype.ofFinite _
  let : Fintype R.FaceOrbit := Fintype.ofFinite _
  have hh := Fintype.card_congr R.componentFacesEquiv
  rw [Fintype.card_sigma] at hh
  simpa only [faceCount,← Nat.card_eq_fintype_card] using hh
end JSP512Probe.RotationSystem
