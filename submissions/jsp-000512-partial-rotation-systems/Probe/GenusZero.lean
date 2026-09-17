import Probe.EulerDefect

namespace JSP512Probe.RotationSystem
variable {V : Type*} [Fintype V] [DecidableEq V]

noncomputable def botComponentEquiv : (⊥ : SimpleGraph V).ConnectedComponent ≃ V where
  toFun := Quotient.lift (s := (⊥ : SimpleGraph V).reachableSetoid) id
    (fun _ _ h => SimpleGraph.reachable_bot.mp h)
  invFun := (⊥ : SimpleGraph V).connectedComponentMk
  left_inv q := by
    change Quotient (⊥ : SimpleGraph V).reachableSetoid at q
    induction q using Quotient.inductionOn with
    | h v => rfl
  right_inv _ := rfl

omit [DecidableEq V] in
theorem bot_defect (R : RotationSystem (⊥ : SimpleGraph V)) : R.eulerDefect = 0 := by
  classical
  have hi : IsEmpty (⊥ : SimpleGraph V).Dart := ⟨fun d => d.adj⟩
  have hf : R.faceCount = 0 := by
    unfold faceCount FaceOrbit
    simp
  have hc := Nat.card_congr (botComponentEquiv (V := V))
  have he : Nat.card (⊥ : SimpleGraph V).edgeSet = 0 := by simp
  simp only [eulerDefect, hf, he, hc, Nat.card_eq_fintype_card]
  have hs : supportSize (G := (⊥ : SimpleGraph V)) = 0 := by simp [supportSize]
  rw [hs]
  omega

/-- Euler's upper bound for every finite rotation system, including disconnected
 graphs and isolated vertices. No planarity assumption is used. -/
theorem defect_nonnegative (G : SimpleGraph V) (R : RotationSystem G) : 0 ≤ R.eulerDefect := by
  classical
  suffices hall : ∀ n : ℕ, ∀ H : SimpleGraph V, Nat.card H.edgeSet = n →
      ∀ S : RotationSystem H, 0 ≤ S.eulerDefect from hall _ G rfl R
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro H hH S
    by_cases hb : H = ⊥
    · subst H
      rw [bot_defect]
    · obtain ⟨u, v, huv⟩ := H.ne_bot_iff_exists_adj.mp hb
      let d : H.Dart := ⟨(u,v),huv⟩
      have he := edge_count_delete d
      have hlt : Nat.card (DeletedGraph d).edgeSet < n := by omega
      have hn := ih _ hlt (DeletedGraph d) rfl (S.deleteEdge d)
      exact le_trans hn (S.defect_delete_le d)

/-- Genus zero expressed solely in terms of permutation orbits and graph counts.
This is not defined using a coloring or recursive decomposition certificate. -/
def HasGenusZero {G : SimpleGraph V} (R : RotationSystem G) : Prop := R.eulerDefect = 0

/-- Genus-zero rotation systems remain genus zero after deleting any edge. -/
theorem genusZero_delete {G : SimpleGraph V} [DecidableRel G.Adj]
    (R : RotationSystem G) (h : R.HasGenusZero) (d : G.Dart) :
    (R.deleteEdge d).HasGenusZero := by
  have hl := R.defect_delete_le d
  have hn := defect_nonnegative _ (R.deleteEdge d)
  unfold HasGenusZero at h ⊢
  omega

/-- In genus zero, a nonbridge must have distinct faces on its two sides. -/
theorem genusZero_nonbridge_faces {G : SimpleGraph V} [DecidableRel G.Adj]
    (R : RotationSystem G) (h : R.HasGenusZero) (d : G.Dart)
    (hb : ¬G.IsBridge d.edge) : ¬R.face.SameCycle d d.symm := by
  intro hf
  obtain ⟨hs, ht⟩ := R.nonbridge_rotations d hb
  have hc := nonbridge_component_count d hb
  have he := edge_count_delete d
  have hv := R.supportSize_delete d
  have hface := R.delete_face_count_same d hs ht hf
  have hn := defect_nonnegative _ (R.deleteEdge d)
  unfold HasGenusZero eulerDefect at h
  unfold eulerDefect at hn
  simp only [ite_eq_right hs, ite_eq_right ht] at hv
  omega

theorem genusZero_bridge_iff_sameFace {G : SimpleGraph V} [DecidableRel G.Adj]
    (R : RotationSystem G) (h : R.HasGenusZero) (d : G.Dart) :
    G.IsBridge d.edge ↔ R.face.SameCycle d d.symm := by
  constructor
  · exact R.bridge_same_face d
  · intro hf
    by_contra hb
    exact R.genusZero_nonbridge_faces h d hb hf

/-- Every spanning subgraph of a genus-zero rotation graph admits a genus-zero
rotation system. The witness is constructed by repeated actual edge deletion. -/
theorem genusZero_subgraph (G H : SimpleGraph V) (R : RotationSystem G)
    (hR : R.HasGenusZero) (hHG : H ≤ G) :
    ∃ S : RotationSystem H, S.HasGenusZero := by
  classical
  suffices hall : ∀ n : ℕ, ∀ G : SimpleGraph V, Nat.card G.edgeSet = n →
      ∀ R : RotationSystem G, R.HasGenusZero → ∀ H : SimpleGraph V,
      H ≤ G → ∃ S : RotationSystem H, S.HasGenusZero from hall _ G rfl R hR H hHG
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro K hK S hS L hLK
    by_cases heq : L = K
    · subst L
      exact ⟨S, hS⟩
    · have hex : ∃ u v, K.Adj u v ∧ ¬L.Adj u v := by
        by_contra h
        push Not at h
        exact heq (le_antisymm hLK h)
      obtain ⟨u, v, huv, hnuv⟩ := hex
      let d : K.Dart := ⟨(u,v),huv⟩
      have hsub : L ≤ DeletedGraph d := by
        intro x y hxy
        apply SimpleGraph.deleteEdges_adj.mpr
        refine ⟨hLK hxy, ?_⟩
        let e : K.Dart := ⟨(x,y),hLK hxy⟩
        change ¬e.edge = d.edge
        rw [SimpleGraph.dart_edge_eq_iff e d]
        rintro (he | he)
        · have h : L.Adj e.fst e.snd := hxy
          rw [he] at h
          exact hnuv h
        · have h : L.Adj e.fst e.snd := hxy
          rw [he] at h
          exact hnuv h.symm
      have hc := edge_count_delete d
      exact ih _ (by omega) (DeletedGraph d) rfl (S.deleteEdge d)
        (S.genusZero_delete hS d) L hsub

end JSP512Probe.RotationSystem
