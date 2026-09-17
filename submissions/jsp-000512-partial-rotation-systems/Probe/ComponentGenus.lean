import Probe.ComponentFaceCounts

namespace JSP512Probe.RotationSystem
variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj] (R : RotationSystem G)

/-- Euler defect of the actual rotation restricted to one component. -/
noncomputable def componentDefect (C : G.ConnectedComponent) : ℤ :=
  letI : Fintype C := Fintype.ofFinite _
  (R.componentRotation C).eulerDefect

theorem componentDefect_nonnegative (C : G.ConnectedComponent) : 0 ≤ R.componentDefect C := by
  classical
  let : Fintype C := Fintype.ofFinite _
  exact defect_nonnegative C.toSimpleGraph (R.componentRotation C)

omit [DecidableEq V] in
/-- The Euler defect is exactly the sum of defects of the actual component rotations. -/
theorem sum_componentDefect [Fintype G.ConnectedComponent] :
    ∑ C : G.ConnectedComponent, R.componentDefect C = R.eulerDefect := by
  classical
  have hv : ∑ C : G.ConnectedComponent, (Nat.card C : ℤ) = Fintype.card V := by
    exact_mod_cast (sum_component_vertices (G := G))
  have hs : ∑ C : G.ConnectedComponent, (Nat.card C.toSimpleGraph.support : ℤ) = Nat.card G.support := by
    exact_mod_cast (sum_component_support (G := G))
  have he : ∑ C : G.ConnectedComponent, (Nat.card C.toSimpleGraph.edgeSet : ℤ) = Nat.card G.edgeSet := by
    exact_mod_cast (sum_component_edges (G := G))
  have hf : ∑ C : G.ConnectedComponent, ((R.componentRotation C).faceCount : ℤ) = R.faceCount := by
    exact_mod_cast R.sum_component_faces
  have form : ∀ C : G.ConnectedComponent, R.componentDefect C =
      2 - 2 * (Nat.card C : ℤ) + Nat.card C.toSimpleGraph.support +
        Nat.card C.toSimpleGraph.edgeSet - (R.componentRotation C).faceCount := by
    intro C
    have hc := component_card_of_connected C.toSimpleGraph C.connected_toSimpleGraph
    simp only [componentDefect,eulerDefect,supportSize,hc,← Nat.card_eq_fintype_card]
    norm_num
  simp only [form,Finset.sum_sub_distrib,Finset.sum_add_distrib,← Finset.mul_sum,
    hv,hs,he,hf,Finset.sum_const,Finset.card_univ]
  simp only [eulerDefect,supportSize,← Nat.card_eq_fintype_card]
  ring

/-- Global zero genus forces every actual component restriction to have zero genus. -/
theorem componentRotation_genusZero (hz : R.HasGenusZero) (C : G.ConnectedComponent) :
    letI : Fintype C := Fintype.ofFinite _
    (R.componentRotation C).HasGenusZero := by
  classical
  let : Fintype G.ConnectedComponent := Fintype.ofFinite _
  have hsum : ∑ D : G.ConnectedComponent, R.componentDefect D = 0 :=
    R.sum_componentDefect.trans hz
  have hh := (Finset.sum_eq_zero_iff_of_nonneg
    (fun D (_ : D ∈ (Finset.univ : Finset G.ConnectedComponent)) => R.componentDefect_nonnegative D)).mp hsum
  exact hh C (Finset.mem_univ C)
end JSP512Probe.RotationSystem
