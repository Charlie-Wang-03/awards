import Probe.ComponentRotation

namespace JSP512Probe.RotationSystem
variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj] [Fintype G.ConnectedComponent]

omit [DecidableEq V] [DecidableRel G.Adj] in
/-- Connected components partition the vertex carrier, including isolates. -/
theorem sum_component_vertices : ∑ C : G.ConnectedComponent, Nat.card C = Fintype.card V := by
  classical
  have hh := Fintype.card_congr (Equiv.sigmaFiberEquiv G.connectedComponentMk)
  rw [Fintype.card_sigma] at hh
  calc
    _ = ∑ C : G.ConnectedComponent, Nat.card {v : V // G.connectedComponentMk v = C} :=
      Finset.sum_congr rfl (fun C _ => Nat.card_congr (Equiv.refl _))
    _ = _ := by simpa only [← Nat.card_eq_fintype_card] using hh

/-- Every dart lies in exactly the component of its source. -/
noncomputable def componentDartsEquiv : (Σ C : G.ConnectedComponent, C.toSimpleGraph.Dart) ≃ G.Dart :=
  (Equiv.sigmaCongrRight (fun C : G.ConnectedComponent => closedDartEquiv C.supp
    (fun _ hu _ huv => C.mem_supp_of_adj_mem_supp hu huv))).trans
      (Equiv.sigmaFiberEquiv (fun d : G.Dart => G.connectedComponentMk d.fst))

omit [DecidableEq V] in
/-- Edge counts add over components. -/
theorem sum_component_edges : ∑ C : G.ConnectedComponent, Nat.card C.toSimpleGraph.edgeSet =
    Nat.card G.edgeSet := by
  classical
  have hh := Fintype.card_congr (componentDartsEquiv (G := G))
  rw [Fintype.card_sigma] at hh
  simp only [SimpleGraph.dart_card_eq_twice_card_edges,SimpleGraph.edgeFinset_card] at hh
  simp only [← Nat.card_eq_fintype_card] at hh
  rw [← Finset.mul_sum] at hh
  omega

/-- Supported vertices partition into supported vertices of the component graphs. -/
noncomputable def componentSupportEquiv :
    (Σ C : G.ConnectedComponent, C.toSimpleGraph.support) ≃ G.support where
  toFun x := ⟨x.2.val.val,by
    obtain ⟨w,hw⟩ := x.1.toSimpleGraph.mem_support.mp x.2.property
    exact G.mem_support.mpr ⟨w.val,hw⟩⟩
  invFun x := ⟨G.connectedComponentMk x.val,⟨⟨x.val,rfl⟩,by
    obtain ⟨w,hw⟩ := G.mem_support.mp x.property
    have hm : w ∈ (G.connectedComponentMk x.val).supp :=
      SimpleGraph.ConnectedComponent.eq.mpr hw.reachable.symm
    exact (G.connectedComponentMk x.val).toSimpleGraph.mem_support.mpr ⟨⟨w,hm⟩,hw⟩⟩⟩
  left_inv x := by
    obtain ⟨C,⟨⟨v,hv⟩,hs⟩⟩ := x
    change G.connectedComponentMk v = C at hv
    subst C
    rfl
  right_inv _ := rfl

omit [DecidableEq V] in
/-- Support sizes add even when singleton isolated components are present. -/
theorem sum_component_support : ∑ C : G.ConnectedComponent, Nat.card C.toSimpleGraph.support =
    Nat.card G.support := by
  classical
  have hh := Fintype.card_congr (componentSupportEquiv (G := G))
  rw [Fintype.card_sigma] at hh
  simpa only [← Nat.card_eq_fintype_card] using hh
end JSP512Probe.RotationSystem
