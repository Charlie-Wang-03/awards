import Probe.FanContinuation

namespace JSP512Probe.CycleSurgery
/-- A three-step return holds at every point in the same finite orbit. -/
theorem three_step_of_sameCycle {α : Type*} [Finite α] (σ : Equiv.Perm α)
    (d x : α) (hd : σ (σ (σ d)) = d) (hx : σ.SameCycle d x) :
    σ (σ (σ x)) = x := by
  rcases (three_step_cycle_iff σ d x hd).mp hx with rfl | rfl | rfl
  · exact hd
  · exact congrArg σ hd
  · exact congrArg (fun z => σ (σ z)) hd
end JSP512Probe.CycleSurgery

namespace JSP512Probe.EdgeInsertion
open RotationSystem CycleSurgery
variable {V : Type*} [Fintype V] [DecidableEq V]
  (G : SimpleGraph V) [DecidableRel G.Adj] (R : RotationSystem G) (a b : G.Dart)
  (hne : a.fst ≠ b.fst) (hm : ¬G.Adj a.fst b.fst)

/-- Every old dart in the modified face lies either in the retained face or
in the new ear after insertion. -/
theorem added_outer_partition (d : G.Dart) (hd : R.face.SameCycle a.symm d) :
    let S := addEdge G R a b hne hm
    let E := dartEquiv G a.fst b.fst hne hm
    S.face.SameCycle (E (some (some a.symm))) (E (some (some d))) ∨
      S.face.SameCycle (E none) (E (some (some d))) := by
  let S := addEdge G R a b hne hm
  let E := dartEquiv G a.fst b.fst hne hm
  obtain ⟨n, rfl⟩ := hd.exists_nat_pow_eq
  clear hd
  induction n with
  | zero => exact Or.inl Equiv.Perm.SameCycle.rfl
  | succ n ih =>
    rw [pow_succ', Equiv.Perm.mul_apply]
    let x := (R.face ^ n) a.symm
    by_cases ha : x = a.symm
    · have he : S.face.SameCycle (E none) (S.face (E none)) :=
        Equiv.Perm.SameCycle.rfl.apply_right
      rw [added_face_reverse] at he
      apply Or.inr
      change S.face.SameCycle (E none) (E (some (some (R.face x))))
      rw [ha]
      exact he
    · by_cases hb : x = b.symm
      · have he : S.face.SameCycle (E (some (some a.symm)))
            (S.face (S.face (E (some (some a.symm))))) :=
          Equiv.Perm.SameCycle.rfl.apply_right.apply_right
        rw [added_face_left, added_face_forward] at he
        change S.face.SameCycle _ (E (some (some (R.face x)))) ∨ _
        rw [hb]
        exact Or.inl he
      · have hs := added_face_old_away G R a b hne hm x ha hb
        rcases ih with ih | ih
        · apply Or.inl
          rw [← hs]
          exact ih.apply_right
        · apply Or.inr
          rw [← hs]
          exact ih.apply_right

/-- Ear insertion preserves triangulation of every face other than the
retained outer face, including the newly split-off face. -/
theorem added_inner_triangles (hpath : R.face (R.rotate a) = b.symm)
    (hinner : ∀ d, ¬R.face.SameCycle a.symm d → R.face (R.face (R.face d)) = d) :
    let S := addEdge G R a b hne hm
    let E := dartEquiv G a.fst b.fst hne hm
    ∀ d, ¬S.face.SameCycle (E (some (some a.symm))) d →
      S.face (S.face (S.face d)) = d := by
  classical
  dsimp only
  let : Fintype (addedGraph G a.fst b.fst hne).Dart :=
    Fintype.ofEquiv (Option (Option G.Dart)) (dartEquiv G a.fst b.fst hne hm)
  let S := addEdge G R a b hne hm
  let E := dartEquiv G a.fst b.fst hne hm
  have hear := added_ear_triangle G R a b hne hm hpath
  have hrev : S.face.SameCycle (E none) (E (some (some (R.rotate a)))) := by
    have hh : S.face.SameCycle (E none) (S.face (E none)) :=
      Equiv.Perm.SameCycle.rfl.apply_right
    simpa only [S, E, added_face_reverse] using hh
  have htri : S.face (S.face (S.face (E none))) = E none :=
    three_step_of_sameCycle S.face _ _ hear hrev.symm
  intro d hd
  obtain ⟨x, rfl⟩ := E.surjective d
  cases x with
  | none => exact htri
  | some x =>
    cases x with
    | none =>
      exfalso
      apply hd
      have hh : S.face.SameCycle (E (some (some a.symm)))
          (S.face (E (some (some a.symm)))) := Equiv.Perm.SameCycle.rfl.apply_right
      simpa only [S, E, added_face_left] using hh
    | some x =>
      by_cases hx : R.face.SameCycle a.symm x
      · have hh := added_outer_partition G R a b hne hm x hx
        rcases hh with hh | hh
        · exact False.elim (hd hh)
        · exact three_step_of_sameCycle S.face _ _ htri hh
      · exact added_ear_preserves_triangle G R a b hne hm hpath x hx (hinner x hx)

end JSP512Probe.EdgeInsertion
