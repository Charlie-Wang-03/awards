import Probe.FaceInsertion
import Probe.GenusZero

namespace JSP512Probe.EdgeInsertion
open RotationSystem
variable {V : Type*} (G : SimpleGraph V) [Fintype V] [DecidableEq V]
  [DecidableRel G.Adj] (R : RotationSystem G) (a b : G.Dart)

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
theorem added_support (hne : a.fst ≠ b.fst) :
    (addedGraph G a.fst b.fst hne).support = G.support := by
  ext x
  constructor
  · intro h
    obtain ⟨y, hy⟩ := (addedGraph G a.fst b.fst hne).mem_support.mp h
    rcases hy with h | h | h
    · exact G.mem_support.mpr ⟨y,h⟩
    · rw [h.1]
      exact a.adj.mem_support_left
    · rw [h.1]
      exact b.adj.mem_support_left
  · intro h
    obtain ⟨y, hy⟩ := G.mem_support.mp h
    exact (addedGraph G a.fst b.fst hne).mem_support.mpr ⟨y,Or.inl hy⟩

omit [DecidableEq V] in
theorem face_reachable (x y : G.Dart) (h : R.face.SameCycle x y) : G.Reachable x.fst y.fst := by
  obtain ⟨n, rfl⟩ := h.exists_nat_pow_eq
  clear h
  induction n with
  | zero => exact SimpleGraph.Reachable.rfl
  | succ n ih =>
    rw [pow_succ', Equiv.Perm.mul_apply]
    exact ih.trans (R.face_step_adj _).reachable

omit [DecidableEq V] in
theorem cofacial_sources_reachable (hf : R.face.SameCycle a.symm b.symm) :
    G.Reachable a.fst b.fst := by
  have h := face_reachable G R a.symm b.symm hf
  exact (a.adj.reachable.trans h).trans b.adj.reachable.symm

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
theorem added_reachable_iff (hne : a.fst ≠ b.fst) (hr : G.Reachable a.fst b.fst) (x y : V) :
    (addedGraph G a.fst b.fst hne).Reachable x y ↔ G.Reachable x y := by
  constructor
  · rintro ⟨p⟩
    have step : ∀ u v, (addedGraph G a.fst b.fst hne).Adj u v → G.Reachable u v := by
      intro u v h
      rcases h with h | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
      · exact h.reachable
      · exact hr
      · exact hr.symm
    induction p with
    | nil => exact SimpleGraph.Reachable.rfl
    | cons h _ ih => exact (step _ _ h).trans ih
  · intro h
    exact h.mono (fun _ _ he => Or.inl he)

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
theorem added_component_count (hne : a.fst ≠ b.fst) (hr : G.Reachable a.fst b.fst) :
    Nat.card (addedGraph G a.fst b.fst hne).ConnectedComponent = Nat.card G.ConnectedComponent := by
  let e : (addedGraph G a.fst b.fst hne).ConnectedComponent ≃ G.ConnectedComponent :=
    Quotient.congr (ra := (addedGraph G a.fst b.fst hne).reachableSetoid)
      (rb := G.reachableSetoid) (Equiv.refl V) (added_reachable_iff G a b hne hr)
  exact Nat.card_congr e

theorem added_edge_count (hne : a.fst ≠ b.fst) (hm : ¬G.Adj a.fst b.fst) :
    Nat.card (addedGraph G a.fst b.fst hne).edgeSet = Nat.card G.edgeSet + 1 := by
  classical
  have he : (addedGraph G a.fst b.fst hne).edgeFinset = insert s(a.fst,b.fst) G.edgeFinset := by
    ext e
    induction e using Sym2.inductionOn with
    | hf x y =>
      simp only [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet, Finset.mem_insert]
      change (G.Adj x y ∨ (x = a.fst ∧ y = b.fst) ∨ (x = b.fst ∧ y = a.fst)) ↔ _
      simp only [Sym2.eq_iff]
      tauto
  have hn : s(a.fst,b.fst) ∉ G.edgeFinset := by simpa using hm
  have hc := Finset.card_insert_of_notMem hn
  rw [← he] at hc
  simpa only [SimpleGraph.edgeFinset, Set.toFinset_card, Nat.card_eq_fintype_card] using hc

/-- Inserting a missing edge at cofacial corners preserves Euler defect. -/
theorem cofacial_defect (hne : a.fst ≠ b.fst) (hm : ¬G.Adj a.fst b.fst)
    (hf : R.face.SameCycle a.symm b.symm) :
    (addEdge G R a b hne hm).eulerDefect = R.eulerDefect := by
  have hc := added_component_count G a b hne (cofacial_sources_reachable G R a b hf)
  have he := added_edge_count G a b hne hm
  have hs := added_support G a b hne
  have hface := cofacial_added_face_count G R a b hne hm hf
  unfold eulerDefect supportSize
  rw [hs]
  omega

/-- Genus-zero preservation for adding a chord at two distinct nonadjacent
nonisolated source corners on the same face. -/
theorem cofacial_genusZero (hne : a.fst ≠ b.fst) (hm : ¬G.Adj a.fst b.fst)
    (hf : R.face.SameCycle a.symm b.symm) (hz : R.HasGenusZero) :
    (addEdge G R a b hne hm).HasGenusZero := by
  unfold HasGenusZero at hz ⊢
  rw [cofacial_defect G R a b hne hm hf, hz]

end JSP512Probe.EdgeInsertion
