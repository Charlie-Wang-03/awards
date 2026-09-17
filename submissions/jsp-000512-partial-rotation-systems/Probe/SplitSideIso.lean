import Probe.SplitSideConnectivity

namespace JSP512Probe.RotationSystem
variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj] (R : RotationSystem G)
  (a b : G.Dart) (hab : a.fst = b.fst)

/-- Projection reflects adjacency when both refined vertices are in one component. -/
theorem split_project_reflects_adj (hne : a ≠ b) (hc : G.Preconnected)
    (hz : R.HasGenusZero) (hf : R.face.SameCycle a b)
    (d e : G.Dart)
    (hr : (RefinedRotation.graph G (R.splitRotation a b) (R.split_source a b hab)).Reachable
      (RefinedRotation.vertex G (R.splitRotation a b) d)
      (RefinedRotation.vertex G (R.splitRotation a b) e))
    (hadj : G.Adj d.fst e.fst) :
    (RefinedRotation.graph G (R.splitRotation a b) (R.split_source a b hab)).Adj
      (RefinedRotation.vertex G (R.splitRotation a b) d)
      (RefinedRotation.vertex G (R.splitRotation a b) e) := by
  let H := RefinedRotation.graph G (R.splitRotation a b) (R.split_source a b hab)
  let q := RefinedRotation.vertex G (R.splitRotation a b)
  have away : ∀ d e : G.Dart, d.fst ≠ a.fst → H.Reachable (q d) (q e) →
      G.Adj d.fst e.fst → H.Adj (q d) (q e) := by
    intro d e hd hr hadj
    let r : G.Dart := ⟨(d.fst,e.fst),hadj⟩
    have hqd : q r = q d := Quotient.sound (R.split_cycles_away a b hab hne r d hd rfl)
    have edge : H.Adj (q r) (q r.symm) := ⟨r,rfl,rfl⟩
    have hreach : H.Reachable (q r.symm) (q e) := by
      apply edge.reachable.symm.trans
      rw [hqd]
      exact hr
    have hqe := R.split_project_injective_on_component a b hab hne hc hz hf r.symm e rfl hreach
    exact ⟨r,hqd,hqe⟩
  by_cases hd : d.fst = a.fst
  · have he : e.fst ≠ a.fst := fun h => hadj.ne (hd.trans h.symm)
    exact (away e d he hr.symm hadj.symm).symm
  · exact away d e hd hr hadj

/-- Each actual split component is isomorphic to its induced projected side. -/
noncomputable def split_component_iso (hne : a ≠ b) (hc : G.Preconnected)
    (hz : R.HasGenusZero) (hf : R.face.SameCycle a b) (mark : G.Dart) :
    ((RefinedRotation.graph G (R.splitRotation a b) (R.split_source a b hab)).connectedComponentMk
      (RefinedRotation.vertex G (R.splitRotation a b) mark)).toSimpleGraph ≃g
    G.induce (R.splitSide a b hab mark) := by
  classical
  let σ := R.splitRotation a b
  let H := RefinedRotation.graph G σ (R.split_source a b hab)
  let q := RefinedRotation.vertex G σ
  let project := RefinedRotation.project G σ (R.split_source a b hab)
  let C := H.connectedComponentMk (q mark)
  have mem : ∀ z : C, project z.val ∈ R.splitSide a b hab mark := by
    rintro ⟨z,hz⟩
    induction z using Quotient.inductionOn with
    | h d => exact ⟨d,rfl,SimpleGraph.ConnectedComponent.eq.mp hz⟩
  let f : C → R.splitSide a b hab mark := fun z => ⟨project z.val,mem z⟩
  have inj : Function.Injective f := by
    rintro ⟨x,hx⟩ ⟨y,hy⟩ he
    apply Subtype.ext
    induction x using Quotient.inductionOn with
    | h d =>
      induction y using Quotient.inductionOn with
      | h e =>
        exact R.split_project_injective_on_component a b hab hne hc hz hf d e
          (congrArg Subtype.val he) (C.reachable_of_mem_supp hx hy)
  have surj : Function.Surjective f := by
    intro u
    obtain ⟨d,hd,hr⟩ := u.property
    have hm : q d ∈ C.supp := SimpleGraph.ConnectedComponent.eq.mpr hr
    exact ⟨⟨q d,hm⟩,Subtype.ext hd⟩
  refine ⟨Equiv.ofBijective f ⟨inj,surj⟩,?_⟩
  intro x y
  constructor
  · intro h
    obtain ⟨x,hx⟩ := x
    obtain ⟨y,hy⟩ := y
    induction x using Quotient.inductionOn with
    | h d =>
      induction y using Quotient.inductionOn with
      | h e =>
        exact R.split_project_reflects_adj a b hab hne hc hz hf d e
          (C.reachable_of_mem_supp hx hy) h
  · intro h
    exact (RefinedRotation.projectHom G σ (R.split_source a b hab)).map_adj h
end JSP512Probe.RotationSystem
