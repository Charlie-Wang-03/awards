import Probe.FaceVertexSimplicity

namespace JSP512Probe.RotationSystem
open CycleSurgery
variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj] (R : RotationSystem G)

omit [Fintype V] [DecidableRel G.Adj] in
/-- Deleting an edge leaves a retained facial step unchanged whenever both
the step's dart and its successor's edge survive. -/
theorem delete_face_step_unchanged (d x : G.Dart)
    (hx : x.edge ≠ d.edge) (hy : (R.face x).edge ≠ d.edge) :
    R.erasedRotation d x.symm = R.face x := by
  change (R.rotate x.symm).edge ≠ d.edge at hy
  have hx' : x.symm ≠ d ∧ x.symm ≠ d.symm := by
    constructor
    · intro h
      exact hx (by simpa only [SimpleGraph.Dart.edge_symm] using congrArg SimpleGraph.Dart.edge h)
    · intro h
      exact hx (by simpa only [SimpleGraph.Dart.edge_symm] using congrArg SimpleGraph.Dart.edge h)
  have hy' : R.rotate x.symm ≠ d ∧ R.rotate x.symm ≠ d.symm := by
    constructor
    · intro h
      exact hy (congrArg SimpleGraph.Dart.edge h)
    · intro h
      exact hy (by simpa only [SimpleGraph.Dart.edge_symm] using congrArg SimpleGraph.Dart.edge h)
  change eraseAt (eraseAt R.rotate d) d.symm x.symm = R.rotate x.symm
  have h₁ : eraseAt R.rotate d x.symm = R.rotate x.symm := by
    rw [eraseAt_apply _ _ _ hx'.1, ite_eq_right hy'.1]
  rw [eraseAt_apply _ _ _ hx'.2, h₁, ite_eq_right hy'.2]

omit [DecidableRel G.Adj] in
/-- A prescribed finite collection of facial steps is retained during spanning
subgraph restriction if the subgraph contains all their edges. -/
theorem genusZero_subgraph_preserving_steps {α : Type*} (π : Equiv.Perm α)
    (H : SimpleGraph V) (hz : R.HasGenusZero) (hHG : H ≤ G)
    (f : α → G.Dart) (hf : ∀ x, f (π x) = R.face (f x))
    (hkeep : ∀ x, H.Adj (f x).fst (f x).snd) :
    ∃ S : RotationSystem H, S.HasGenusZero ∧ ∃ g : α → H.Dart,
      (∀ x, (g x).toProd = (f x).toProd) ∧ (∀ x, g (π x) = S.face (g x)) := by
  classical
  suffices hall : ∀ n : ℕ, ∀ K : SimpleGraph V, Nat.card K.edgeSet = n →
      ∀ T : RotationSystem K, T.HasGenusZero → ∀ L : SimpleGraph V, L ≤ K →
      ∀ f : α → K.Dart, (∀ x, f (π x) = T.face (f x)) →
      (∀ x, L.Adj (f x).fst (f x).snd) →
      ∃ S : RotationSystem L, S.HasGenusZero ∧ ∃ g : α → L.Dart,
        (∀ x, (g x).toProd = (f x).toProd) ∧ (∀ x, g (π x) = S.face (g x)) from
    hall _ G rfl R hz H hHG f hf hkeep
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro K hK T hT L hLK f hf hkeep
    by_cases heq : L = K
    · subst L
      exact ⟨T,hT,f,fun _ => rfl,hf⟩
    · have hex : ∃ u v, K.Adj u v ∧ ¬L.Adj u v := by
        by_contra h
        push Not at h
        exact heq (le_antisymm hLK h)
      obtain ⟨u,v,huv,hnuv⟩ := hex
      let d : K.Dart := ⟨(u,v),huv⟩
      have survivor : ∀ e : K.Dart, L.Adj e.fst e.snd → e.edge ≠ d.edge := by
        intro e he h
        rcases (SimpleGraph.dart_edge_eq_iff e d).mp h with h | h
        · rw [h] at he
          exact hnuv he
        · rw [h] at he
          exact hnuv he.symm
      have hsub : L ≤ DeletedGraph d := by
        intro x y hxy
        exact SimpleGraph.deleteEdges_adj.mpr ⟨hLK hxy,
          survivor ⟨(x,y),hLK hxy⟩ hxy⟩
      let f' (x : α) : (DeletedGraph d).Dart :=
        (deletedDartEquiv d).symm ⟨f x,survivor (f x) (hkeep x)⟩
      have hprod : ∀ x, (f' x).toProd = (f x).toProd := fun _ => rfl
      have hstep : ∀ x, f' (π x) = (T.deleteEdge d).face (f' x) := by
        intro x
        apply (deletedDartEquiv d).injective
        apply Subtype.ext
        rw [T.deleted_face]
        change f (π x) = T.erasedRotation d (f x).symm
        rw [T.delete_face_step_unchanged d (f x) (survivor _ (hkeep x))]
        · exact hf x
        · rw [← hf x]
          exact survivor _ (hkeep (π x))
      have hc := edge_count_delete d
      obtain ⟨S,hS,g,hg,hstepg⟩ := ih _ (by omega) (DeletedGraph d) rfl
        (T.deleteEdge d) (T.genusZero_delete hT d) L hsub f' hstep (fun x => hkeep x)
      exact ⟨S,hS,g,fun x => (hg x).trans (hprod x),hstepg⟩

end JSP512Probe.RotationSystem
