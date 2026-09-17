import Probe.BridgeFace

namespace JSP512Probe
namespace RotationSystem
variable {V : Type*} {G : SimpleGraph V} (d : G.Dart)

/-- A path through the removed edge can be rerouted if its endpoints remain connected. -/
theorem delete_reachable_iff
    (hd : (DeletedGraph d).Reachable d.fst d.snd) (x y : V) :
    (DeletedGraph d).Reachable x y ↔ G.Reachable x y := by
  constructor
  · exact fun h => h.mono (G.deleteEdges_le _)
  · intro h
    have hstep : ∀ u v, G.Adj u v → (DeletedGraph d).Reachable u v := by
      intro u v huv
      let e : G.Dart := ⟨(u,v), huv⟩
      by_cases he : e.edge = d.edge
      · rcases (SimpleGraph.dart_edge_eq_iff e d).mp he with he | he
        · change (DeletedGraph d).Reachable e.fst e.snd
          rw [he]
          exact hd
        · change (DeletedGraph d).Reachable e.fst e.snd
          rw [he]
          exact hd.symm
      · apply SimpleGraph.Adj.reachable
        apply SimpleGraph.deleteEdges_adj.mpr
        exact ⟨huv, he⟩
    obtain ⟨p⟩ := h
    induction p with
    | nil => exact SimpleGraph.Reachable.rfl
    | cons huv _ ih => exact (hstep _ _ huv).trans ih

/-- Nonbridge deletion preserves the entire connected-component quotient. -/
noncomputable def nonbridgeComponentEquiv (hd : ¬G.IsBridge d.edge) :
    (DeletedGraph d).ConnectedComponent ≃ G.ConnectedComponent := by
  have hr : (DeletedGraph d).Reachable d.fst d.snd := Classical.not_not.mp hd
  exact Quotient.congr (ra := (DeletedGraph d).reachableSetoid) (rb := G.reachableSetoid) (Equiv.refl V) (delete_reachable_iff d hr)

theorem nonbridge_component_count [Finite V] (hd : ¬G.IsBridge d.edge) :
    Nat.card (DeletedGraph d).ConnectedComponent = Nat.card G.ConnectedComponent :=
  Nat.card_congr (nonbridgeComponentEquiv d hd)

noncomputable def componentLabel (x : V) : (DeletedGraph d).ConnectedComponent := by
  classical
  exact if (DeletedGraph d).connectedComponentMk x = (DeletedGraph d).connectedComponentMk d.snd
    then (DeletedGraph d).connectedComponentMk d.fst else (DeletedGraph d).connectedComponentMk x

/-- Restoring the deleted edge identifies exactly its two component labels. -/
theorem reachable_componentLabel (x y : V) :
    G.Reachable x y ↔ componentLabel d x = componentLabel d y := by
  classical
  let q := (DeletedGraph d).connectedComponentMk
  have old : ∀ u v, q u = q v → G.Reachable u v := by
    intro u v h
    exact (SimpleGraph.ConnectedComponent.eq.mp h).mono (G.deleteEdges_le _)
  have joined : componentLabel d d.fst = componentLabel d d.snd := by simp [componentLabel]
  constructor
  · rintro ⟨p⟩
    have step : ∀ u v, G.Adj u v → componentLabel d u = componentLabel d v := by
      intro u v huv
      let e : G.Dart := ⟨(u,v), huv⟩
      by_cases he : e.edge = d.edge
      · rcases (SimpleGraph.dart_edge_eq_iff e d).mp he with he | he
        · change componentLabel d e.fst = componentLabel d e.snd
          rw [he]
          exact joined
        · change componentLabel d e.fst = componentLabel d e.snd
          rw [he]
          exact joined.symm
      · have ha : (DeletedGraph d).Adj u v := SimpleGraph.deleteEdges_adj.mpr ⟨huv, he⟩
        have hq := SimpleGraph.ConnectedComponent.eq.mpr ha.reachable
        unfold componentLabel
        rw [hq]
    induction p with
    | nil => rfl
    | cons huv _ ih => exact (step _ _ huv).trans ih
  · intro h
    change (if q x = q d.snd then q d.fst else q x) =
      (if q y = q d.snd then q d.fst else q y) at h
    by_cases hx : q x = q d.snd
    · by_cases hy : q y = q d.snd
      · exact (old x d.snd hx).trans (old y d.snd hy).symm
      · simp only [ite_eq_left hx, ite_eq_right hy] at h
        exact ((old x d.snd hx).trans d.adj.reachable.symm).trans (old d.fst y h)
    · by_cases hy : q y = q d.snd
      · simp only [ite_eq_right hx, ite_eq_left hy] at h
        exact ((old x d.fst h).trans d.adj.reachable).trans (old y d.snd hy).symm
      · simp only [ite_eq_right hx, ite_eq_right hy] at h
        exact old x y h

/-- When the deleted edge is a bridge, the component quotient gains one element. -/
noncomputable def bridgeComponentEquiv (hb : G.IsBridge d.edge) :
    G.ConnectedComponent ≃ {q : (DeletedGraph d).ConnectedComponent //
      q ≠ (DeletedGraph d).connectedComponentMk d.snd} := by
  classical
  have hab : (DeletedGraph d).connectedComponentMk d.fst ≠
      (DeletedGraph d).connectedComponentMk d.snd := by
    intro h
    exact hb (SimpleGraph.ConnectedComponent.eq.mp h)
  let f : G.ConnectedComponent → {q : (DeletedGraph d).ConnectedComponent //
      q ≠ (DeletedGraph d).connectedComponentMk d.snd} :=
    Quotient.lift (s := G.reachableSetoid) (fun x => ⟨componentLabel d x, by
      unfold componentLabel
      split_ifs with h
      · exact hab
      · exact h⟩)
      (by
        intro x y h
        apply Subtype.ext
        exact (reachable_componentLabel d x y).mp h)
  apply Equiv.ofBijective f
  constructor
  · intro x y
    change Quotient G.reachableSetoid at x y
    induction x using Quotient.inductionOn with
    | h x =>
      induction y using Quotient.inductionOn with
      | h y =>
        intro h
        exact Quotient.sound ((reachable_componentLabel d x y).mpr (congrArg Subtype.val h))
  · intro q
    obtain ⟨x, hx⟩ := @Quotient.exists_rep V (DeletedGraph d).reachableSetoid q.val
    refine ⟨G.connectedComponentMk x, ?_⟩
    apply Subtype.ext
    change componentLabel d x = q.val
    unfold componentLabel
    change (if (Quotient.mk (DeletedGraph d).reachableSetoid x) =
      (DeletedGraph d).connectedComponentMk d.snd then
      (DeletedGraph d).connectedComponentMk d.fst else
      Quotient.mk (DeletedGraph d).reachableSetoid x) = q.val
    rw [hx]
    split_ifs with h
    · exact False.elim (q.property h)
    · rfl

theorem bridge_component_count [Finite V] (hb : G.IsBridge d.edge) :
    Nat.card (DeletedGraph d).ConnectedComponent = Nat.card G.ConnectedComponent + 1 := by
  classical
  let Q := (DeletedGraph d).ConnectedComponent
  let := Fintype.ofFinite Q
  let := Fintype.ofFinite G.ConnectedComponent
  have he := Nat.card_congr (bridgeComponentEquiv d hb)
  have hc := Fintype.card_subtype_compl
    (fun q : Q => q = (DeletedGraph d).connectedComponentMk d.snd)
  have hp : 0 < Fintype.card Q := Fintype.card_pos_iff.mpr
    ⟨(DeletedGraph d).connectedComponentMk d.snd⟩
  simp only [Nat.card_eq_fintype_card] at he ⊢
  simp only [Fintype.card_unique] at hc
  dsimp only [Q] at hc hp
  simp only [ne_eq] at he hc
  omega

end RotationSystem
end JSP512Probe
