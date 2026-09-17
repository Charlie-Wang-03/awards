import Probe.CycleInsertion

namespace JSP512Probe
namespace EdgeInsertion
variable {V : Type*} (G : SimpleGraph V) (u v : V) (hne : u ≠ v)

/-- Add exactly the missing undirected edge, on the original vertex type. -/
def addedGraph : SimpleGraph V where
  Adj x y := G.Adj x y ∨ (x = u ∧ y = v) ∨ (x = v ∧ y = u)
  symm := ⟨by
    intro x y h
    rcases h with h | h | h
    · exact Or.inl h.symm
    · exact Or.inr (Or.inr ⟨h.2,h.1⟩)
    · exact Or.inr (Or.inl ⟨h.2,h.1⟩)⟩
  loopless := ⟨by
    intro x h
    rcases h with h | h | h
    · exact G.irrefl h
    · exact hne (h.1.symm.trans h.2)
    · exact hne (h.2.symm.trans h.1)⟩

/-- `none` is the new dart from v to u; `some none` is from u to v. -/
def embedDart : Option (Option G.Dart) → (addedGraph G u v hne).Dart
  | none => ⟨(v,u), Or.inr (Or.inr ⟨rfl,rfl⟩)⟩
  | some none => ⟨(u,v), Or.inr (Or.inl ⟨rfl,rfl⟩)⟩
  | some (some d) => ⟨d.toProd, Or.inl d.adj⟩

theorem embedDart_injective (hmissing : ¬G.Adj u v) :
    Function.Injective (embedDart G u v hne) := by
  intro x y h
  have hp := congrArg (fun d : (addedGraph G u v hne).Dart => d.toProd) h
  cases x with
  | none =>
    cases y with
    | none => rfl
    | some y =>
      cases y with
      | none => exact False.elim (hne (congrArg Prod.snd hp))
      | some e =>
        have he : G.Adj v u := by
          have he := e.adj
          change (v,u) = e.toProd at hp
          simpa only [← hp] using he
        exact False.elim (hmissing he.symm)
  | some x =>
    cases x with
    | none =>
      cases y with
      | none => exact False.elim (hne (congrArg Prod.fst hp))
      | some y =>
        cases y with
        | none => rfl
        | some e =>
          have he : G.Adj u v := by
            have he := e.adj
            change (u,v) = e.toProd at hp
            simpa only [← hp] using he
          exact False.elim (hmissing he)
    | some e =>
      cases y with
      | none =>
        have he : G.Adj v u := by
          have he := e.adj
          change e.toProd = (v,u) at hp
          simpa only [hp] using he
        exact False.elim (hmissing he.symm)
      | some y =>
        cases y with
        | none =>
          have he : G.Adj u v := by
            have he := e.adj
            change e.toProd = (u,v) at hp
            simpa only [hp] using he
          exact False.elim (hmissing he)
        | some f => exact congrArg (fun z => some (some z)) (SimpleGraph.Dart.ext e f hp)

theorem embedDart_surjective : Function.Surjective (embedDart G u v hne) := by
  intro d
  rcases d.adj with h | h | h
  · exact ⟨some (some ⟨d.toProd,h⟩), SimpleGraph.Dart.ext _ _ rfl⟩
  · refine ⟨some none, SimpleGraph.Dart.ext _ _ ?_⟩
    exact Prod.ext h.1.symm h.2.symm
  · refine ⟨none, SimpleGraph.Dart.ext _ _ ?_⟩
    exact Prod.ext h.1.symm h.2.symm

noncomputable def dartEquiv (hmissing : ¬G.Adj u v) :
    Option (Option G.Dart) ≃ (addedGraph G u v hne).Dart :=
  Equiv.ofBijective (embedDart G u v hne)
    ⟨embedDart_injective G u v hne hmissing, embedDart_surjective G u v hne⟩

/-- Reverse the two new darts and reverse every original dart. -/
def extendedReverse : Equiv.Perm (Option (Option G.Dart)) where
  toFun
    | none => some none
    | some none => none
    | some (some d) => some (some d.symm)
  invFun
    | none => some none
    | some none => none
    | some (some d) => some (some d.symm)
  left_inv x := by
    cases x with
    | none => rfl
    | some x => cases x <;> simp [SimpleGraph.Dart.symm_symm]
  right_inv x := by
    cases x with
    | none => rfl
    | some x => cases x <;> simp [SimpleGraph.Dart.symm_symm]

theorem embed_reverse (x : Option (Option G.Dart)) :
    embedDart G u v hne (extendedReverse G x) = (embedDart G u v hne x).symm := by
  cases x with
  | none => rfl
  | some x => cases x <;> rfl

section Rotation
variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
  (R : RotationSystem G) (a b : G.Dart)
open CycleSurgery

/-- Insert the two new darts at the specified source corners. -/
def cornerRotation : Equiv.Perm (Option (Option G.Dart)) :=
  insertAfter (insertAfter R.rotate a) (some b)

theorem corner_cycles (hne : a.fst ≠ b.fst) (x y : Option (Option G.Dart)) :
    (cornerRotation G R a b).SameCycle x y ↔
      (embedDart G a.fst b.fst hne x).fst = (embedDart G a.fst b.fst hne y).fst := by
  have h₁ := insertAfter_fiber_cycles R.rotate (fun d : G.Dart => d.fst)
    R.sameCycle_iff_source a
  have h₂ := insertAfter_fiber_cycles (insertAfter R.rotate a)
    (insertedLabel (fun d : G.Dart => d.fst) a) h₁ (some b) x y
  have hl : ∀ z : Option (Option G.Dart),
      insertedLabel (insertedLabel (fun d : G.Dart => d.fst) a) (some b) z =
        (embedDart G a.fst b.fst hne z).fst := by
    intro z
    cases z with
    | none => rfl
    | some z => cases z <;> rfl
  rw [hl, hl] at h₂
  exact h₂

noncomputable def addedRotation (hne : a.fst ≠ b.fst) (hm : ¬G.Adj a.fst b.fst) :
    Equiv.Perm (addedGraph G a.fst b.fst hne).Dart :=
  (((dartEquiv G a.fst b.fst hne hm).symm).trans (cornerRotation G R a b)).trans
    (dartEquiv G a.fst b.fst hne hm)

theorem added_cycles (hne : a.fst ≠ b.fst) (hm : ¬G.Adj a.fst b.fst)
    (x y : (addedGraph G a.fst b.fst hne).Dart) :
    (addedRotation G R a b hne hm).SameCycle x y ↔ x.fst = y.fst := by
  let e := dartEquiv G a.fst b.fst hne hm
  change Equiv.Perm.SameCycle ((e.symm.trans (cornerRotation G R a b)).trans e) x y ↔ _
  have ht := transport_cycles e.symm (cornerRotation G R a b) x y
  simp only [Equiv.symm_symm] at ht
  rw [ht, corner_cycles G R a b hne]
  change (e (e.symm x)).fst = (e (e.symm y)).fst ↔ _
  rw [e.apply_symm_apply, e.apply_symm_apply]

/-- A genuine rotation system on the graph with one new edge, for two
nonisolated endpoints with chosen insertion corners. No genus claim is made. -/
noncomputable def addEdge (hne : a.fst ≠ b.fst) (hm : ¬G.Adj a.fst b.fst) :
    RotationSystem (addedGraph G a.fst b.fst hne) where
  rotate := addedRotation G R a b hne hm
  source _x := (added_cycles G R a b hne hm _ _).mp Equiv.Perm.SameCycle.rfl.apply_left
  local_cycle x y h := (added_cycles G R a b hne hm x y).mpr h

/-- The face successor of the actual augmented graph is transported from the
explicit two-dart extension; this is the interface for a future face-count proof. -/
theorem added_face_embed (hne : a.fst ≠ b.fst) (hm : ¬G.Adj a.fst b.fst)
    (x : Option (Option G.Dart)) :
    (addEdge G R a b hne hm).face (dartEquiv G a.fst b.fst hne hm x) =
      dartEquiv G a.fst b.fst hne hm (cornerRotation G R a b (extendedReverse G x)) := by
  let e := dartEquiv G a.fst b.fst hne hm
  change e (cornerRotation G R a b (e.symm ((e x).symm))) = _
  have hr : e (extendedReverse G x) = (e x).symm := embed_reverse G _ _ hne x
  rw [← hr, e.symm_apply_apply]

end Rotation
end EdgeInsertion
end JSP512Probe
