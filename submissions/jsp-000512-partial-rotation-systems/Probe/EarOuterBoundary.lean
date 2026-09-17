import Probe.EarInnerFaces

namespace JSP512Probe.EdgeInsertion
open RotationSystem CycleSurgery
variable {V : Type*} [Fintype V] [DecidableEq V]
  (G : SimpleGraph V) [DecidableRel G.Adj] (R : RotationSystem G) (a b : G.Dart)
  (hne : a.fst ≠ b.fst) (hm : ¬G.Adj a.fst b.fst)

/-- An old dart on the retained new face came from the modified old face. -/
theorem added_outer_projects (hpath : R.face (R.rotate a) = b.symm)
    (d : G.Dart)
    (hd : (addEdge G R a b hne hm).face.SameCycle
      (dartEquiv G a.fst b.fst hne hm (some (some a.symm)))
      (dartEquiv G a.fst b.fst hne hm (some (some d)))) :
    R.face.SameCycle a.symm d := by
  classical
  let : Fintype (addedGraph G a.fst b.fst hne).Dart :=
    Fintype.ofEquiv (Option (Option G.Dart)) (dartEquiv G a.fst b.fst hne hm)
  let S := addEdge G R a b hne hm
  let E := dartEquiv G a.fst b.fst hne hm
  have ha : R.face.SameCycle a.symm (R.rotate a) := by
    exact Equiv.Perm.SameCycle.rfl.apply_right
  have hb : R.face.SameCycle a.symm b.symm := by
    rw [← hpath]
    exact ha.apply_right
  let P := fun y => y = E none ∨ y = E (some none) ∨
    ∃ x, R.face.SameCycle a.symm x ∧ y = E (some (some x))
  have step : ∀ y, P y → P (S.face y) := by
    intro y hy
    rcases hy with rfl | rfl | ⟨x, hx, rfl⟩
    · exact Or.inr (Or.inr ⟨R.rotate a, ha, added_face_reverse G R a b hne hm⟩)
    · exact Or.inr (Or.inr ⟨R.rotate b, hb.apply_right, added_face_forward G R a b hne hm⟩)
    · by_cases hxA : x = a.symm
      · subst x
        exact Or.inr (Or.inl (added_face_left G R a b hne hm))
      · by_cases hxB : x = b.symm
        · subst x
          exact Or.inl (added_face_right G R a b hne hm)
        · exact Or.inr (Or.inr ⟨R.face x, hx.apply_right,
            added_face_old_away G R a b hne hm x hxA hxB⟩)
  have all : ∀ n : ℕ, P ((S.face ^ n) (E (some (some a.symm)))) := by
    intro n
    induction n with
    | zero => exact Or.inr (Or.inr ⟨a.symm, Equiv.Perm.SameCycle.rfl, rfl⟩)
    | succ n ih =>
      rw [pow_succ', Equiv.Perm.mul_apply]
      exact step _ ih
  obtain ⟨n, hn⟩ := hd.exists_nat_pow_eq
  have hp := all n
  change P ((S.face ^ n) (E (some (some a.symm)))) at hp
  rw [show (S.face ^ n) (E (some (some a.symm))) = E (some (some d)) from hn] at hp
  rcases hp with he | he | ⟨x, hx, he⟩
  · have hh := E.injective he
    simp at hh
  · have hh := E.injective he
    simp at hh
  · have hh : d = x := Option.some.inj (Option.some.inj (E.injective he))
    exact hh ▸ hx

/-- The retained face and the new ear are distinct. -/
theorem added_outer_not_ear (hpath : R.face (R.rotate a) = b.symm) :
    ¬(addEdge G R a b hne hm).face.SameCycle
      (dartEquiv G a.fst b.fst hne hm (some (some a.symm)))
      (dartEquiv G a.fst b.fst hne hm none) := by
  intro hh
  have hc : (addEdge G R a b hne hm).face.SameCycle
      (dartEquiv G a.fst b.fst hne hm (some (some a.symm)))
      (dartEquiv G a.fst b.fst hne hm (some none)) := by
    have h := Equiv.Perm.SameCycle.rfl (f := (addEdge G R a b hne hm).face)
      (x := dartEquiv G a.fst b.fst hne hm (some (some a.symm)))
    have h' := h.apply_right
    rwa [added_face_left] at h'
  exact added_ear_forward_separate G R a b hne hm hpath (hh.symm.trans hc)

/-- Exact old-dart boundary membership: the two old ear sides are removed,
and every other dart of the old face remains on the retained face. -/
theorem added_outer_old_iff (hpath : R.face (R.rotate a) = b.symm) (d : G.Dart) :
    (addEdge G R a b hne hm).face.SameCycle
      (dartEquiv G a.fst b.fst hne hm (some (some a.symm)))
      (dartEquiv G a.fst b.fst hne hm (some (some d))) ↔
    R.face.SameCycle a.symm d ∧ d ≠ R.rotate a ∧ d ≠ b.symm := by
  have he := added_ear_cycle_iff G R a b hne hm hpath (some (some d))
  dsimp only at he
  simp only [Option.some_ne_none, Option.some.injEq, false_or] at he
  have hsep := added_outer_not_ear G R a b hne hm hpath
  constructor
  · intro hd
    refine ⟨added_outer_projects G R a b hne hm hpath d hd, ?_, ?_⟩
    · intro hh
      exact hsep (hd.trans ((he.mpr (Or.inl hh)).symm))
    · intro hh
      exact hsep (hd.trans ((he.mpr (Or.inr hh)).symm))
  · rintro ⟨hd, ha, hb⟩
    rcases added_outer_partition G R a b hne hm d hd with hh | hh
    · exact hh
    · rcases he.mp hh with hh | hh
      · exact False.elim (ha hh)
      · exact False.elim (hb hh)

/-- Every new outer dart is represented by an old outer dart with the same
source; the forward spoke replaces the first old ear side. -/
theorem added_outer_representative (hpath : R.face (R.rotate a) = b.symm)
    (x : (addedGraph G a.fst b.fst hne).Dart)
    (hx : (addEdge G R a b hne hm).face.SameCycle
      (dartEquiv G a.fst b.fst hne hm (some (some a.symm))) x) :
    ∃ d : G.Dart, R.face.SameCycle a.symm d ∧ d ≠ b.symm ∧ x.fst = d.fst ∧
      x = if d = R.rotate a then dartEquiv G a.fst b.fst hne hm (some none)
        else dartEquiv G a.fst b.fst hne hm (some (some d)) := by
  classical
  let E := dartEquiv G a.fst b.fst hne hm
  obtain ⟨y, rfl⟩ := E.surjective x
  cases y with
  | none => exact False.elim (added_outer_not_ear G R a b hne hm hpath hx)
  | some y =>
    cases y with
    | none =>
      have hb : R.rotate a ≠ b.symm := by
        intro hh
        exact R.face_ne_self (R.rotate a) (hpath.trans hh.symm)
      refine ⟨R.rotate a, Equiv.Perm.SameCycle.rfl.apply_right, hb, ?_, ?_⟩
      · exact (R.source a).symm
      · simp only [ite_true]
        rfl
    | some d =>
      have hd := (added_outer_old_iff G R a b hne hm hpath d).mp hx
      exact ⟨d, hd.1, hd.2.2, rfl, by simp only [ite_eq_right hd.2.1]; rfl⟩

/-- Cutting off an ear preserves source simplicity of the retained outer
face whenever the original outer face is source-simple. -/
theorem added_outer_simple (hpath : R.face (R.rotate a) = b.symm)
    (hsimple : ∀ d e, R.face.SameCycle a.symm d → R.face.SameCycle a.symm e →
      d.fst = e.fst → d = e) :
    let S := addEdge G R a b hne hm
    let E := dartEquiv G a.fst b.fst hne hm
    ∀ x y, S.face.SameCycle (E (some (some a.symm))) x →
      S.face.SameCycle (E (some (some a.symm))) y → x.fst = y.fst → x = y := by
  dsimp only
  intro x y hx hy hxy
  obtain ⟨d, hd, _, hdx, hxd⟩ := added_outer_representative G R a b hne hm hpath x hx
  obtain ⟨e, he, _, hey, hye⟩ := added_outer_representative G R a b hne hm hpath y hy
  have hde := hsimple d e hd he (hdx.symm.trans (hxy.trans hey))
  subst e
  exact hxd.trans hye.symm

end JSP512Probe.EdgeInsertion
