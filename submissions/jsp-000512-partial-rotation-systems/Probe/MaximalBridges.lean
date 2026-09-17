import Probe.MaximalAugmentation

namespace JSP512Probe.RotationSystem
variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]
  (R : RotationSystem G) (hz : R.HasGenusZero) (hmax : EdgeMaximalGenusZero G)

include hz hmax

/-- A bridge in a maximal genus-zero graph cannot have another edge at its source:
a common-face chord would otherwise give an alternate path around the bridge. -/
theorem maximal_bridge_source_fixed (d : G.Dart) (hb : G.IsBridge d.edge) : R.rotate d = d := by
  by_contra hn
  let x := R.face.symm d
  have hs : x.snd = d.fst := R.face_inverse_target d
  have hxu : x.fst ≠ d.fst := by
    rw [← hs]
    exact x.fst_ne_snd
  have hxv : x.fst ≠ d.snd := by
    intro he
    have hx : x = d.symm := SimpleGraph.Dart.ext _ _ (Prod.ext he hs)
    have hf : R.face d.symm = d := by
      rw [← hx]
      exact R.face.apply_symm_apply d
    change R.rotate d.symm.symm = d at hf
    exact hn (by simpa only [SimpleGraph.Dart.symm_symm] using hf)
  have hface : R.face.SameCycle x d.symm := (R.bridge_same_face d hb).symm_apply_left
  have ha : G.Adj x.fst d.snd := R.maximal_face_vertices_adj hz hmax x d.symm hxv hface
  have h₁ : (DeletedGraph d).Adj d.fst x.fst := by
    apply SimpleGraph.deleteEdges_adj.mpr
    constructor
    · rw [← hs]
      exact x.adj.symm
    · change ¬s(d.fst,x.fst) = s(d.fst,d.snd)
      simp only [Sym2.eq_iff]
      tauto
  have h₂ : (DeletedGraph d).Adj x.fst d.snd := by
    apply SimpleGraph.deleteEdges_adj.mpr
    constructor
    · exact ha
    · change ¬s(x.fst,d.snd) = s(d.fst,d.snd)
      simp only [Sym2.eq_iff]
      tauto
  exact hb (h₁.reachable.trans h₂.reachable)

/-- Every bridge in a maximal genus-zero graph is an isolated two-vertex
component. Connectedness of maximal extensions still needs a separate proof. -/
theorem maximal_bridge_endpoints_fixed (d : G.Dart) (hb : G.IsBridge d.edge) :
    R.rotate d = d ∧ R.rotate d.symm = d.symm := by
  refine ⟨R.maximal_bridge_source_fixed hz hmax d hb, ?_⟩
  apply R.maximal_bridge_source_fixed hz hmax d.symm
  simpa only [SimpleGraph.Dart.edge_symm] using hb

end JSP512Probe.RotationSystem
