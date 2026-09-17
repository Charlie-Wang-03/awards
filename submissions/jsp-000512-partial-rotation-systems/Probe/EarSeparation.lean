import Probe.EarInsertion

namespace JSP512Probe.CycleSurgery

/-- A three-step return determines the entire orbit, not just its length. -/
theorem three_step_cycle_iff {α : Type*} [Finite α] (σ : Equiv.Perm α)
    (d x : α) (h : σ (σ (σ d)) = d) :
    σ.SameCycle d x ↔ x = d ∨ x = σ d ∨ x = σ (σ d) := by
  constructor
  · intro hx
    obtain ⟨n, hn⟩ := hx.exists_nat_pow_eq
    have hp : ∀ n : ℕ, (σ ^ n) d = d ∨ (σ ^ n) d = σ d ∨
        (σ ^ n) d = σ (σ d) := by
      intro n
      induction n with
      | zero => exact Or.inl rfl
      | succ n ih =>
        rw [pow_succ', Equiv.Perm.mul_apply]
        rcases ih with hh | hh | hh
        · exact Or.inr (Or.inl (congrArg σ hh))
        · exact Or.inr (Or.inr (congrArg σ hh))
        · exact Or.inl ((congrArg σ hh).trans h)
    simpa only [hn] using hp n
  · rintro (rfl | rfl | rfl)
    · exact Equiv.Perm.SameCycle.rfl
    · exact Equiv.Perm.SameCycle.rfl.apply_right
    · exact Equiv.Perm.SameCycle.rfl.apply_right.apply_right

end JSP512Probe.CycleSurgery

namespace JSP512Probe.EdgeInsertion
open RotationSystem CycleSurgery
variable {V : Type*} [Fintype V] [DecidableEq V]
  (G : SimpleGraph V) [DecidableRel G.Adj] (R : RotationSystem G) (a b : G.Dart)
  (hne : a.fst ≠ b.fst) (hm : ¬G.Adj a.fst b.fst)

/-- The ear consists exactly of its two old sides and the new reverse dart. -/
theorem added_ear_cycle_iff (hpath : R.face (R.rotate a) = b.symm)
    (x : Option (Option G.Dart)) :
    let S := addEdge G R a b hne hm
    let E := dartEquiv G a.fst b.fst hne hm
    S.face.SameCycle (E none) (E x) ↔
      x = none ∨ x = some (some (R.rotate a)) ∨ x = some (some b.symm) := by
  classical
  let : Fintype (addedGraph G a.fst b.fst hne).Dart :=
    Fintype.ofEquiv (Option (Option G.Dart)) (dartEquiv G a.fst b.fst hne hm)
  dsimp only
  have ha : R.rotate a ≠ a.symm := by
    intro h
    have hh := congrArg (fun d : G.Dart => d.fst) h
    rw [R.source] at hh
    exact a.fst_ne_snd hh
  have hb : R.rotate a ≠ b.symm := by
    intro h
    exact R.face_ne_self (R.rotate a) (hpath.trans h.symm)
  have hs := added_face_old_away G R a b hne hm (R.rotate a) ha hb
  rw [hpath] at hs
  have ht : (addEdge G R a b hne hm).face
      ((addEdge G R a b hne hm).face
        ((addEdge G R a b hne hm).face (dartEquiv G a.fst b.fst hne hm none))) =
      dartEquiv G a.fst b.fst hne hm none := by
    rw [added_face_reverse, hs, added_face_right]
  rw [three_step_cycle_iff _ _ _ ht, added_face_reverse, hs]
  simp only [Equiv.apply_eq_iff_eq]

/-- The forward dart stays off the newly created triangular face. -/
theorem added_ear_forward_separate (hpath : R.face (R.rotate a) = b.symm) :
    let S := addEdge G R a b hne hm
    let E := dartEquiv G a.fst b.fst hne hm
    ¬S.face.SameCycle (E none) (E (some none)) := by
  dsimp only
  have hh := added_ear_cycle_iff G R a b hne hm hpath (some none)
  dsimp only at hh
  rw [hh]
  simp

noncomputable local instance : DecidableRel (addedGraph G a.fst b.fst hne).Adj := Classical.decRel _

/-- Any later ear inserted on the forward dart's face preserves this ear. -/
theorem added_ear_survives_next (hpath : R.face (R.rotate a) = b.symm)
    (c e : (addedGraph G a.fst b.fst hne).Dart)
    (hne' : c.fst ≠ e.fst) (hm' : ¬(addedGraph G a.fst b.fst hne).Adj c.fst e.fst)
    (hnext : (addEdge G R a b hne hm).face ((addEdge G R a b hne hm).rotate c) = e.symm)
    (hcorner : (addEdge G R a b hne hm).face.SameCycle
      (dartEquiv G a.fst b.fst hne hm (some none)) c.symm) :
    let S := addEdge G R a b hne hm
    let T := addEdge (addedGraph G a.fst b.fst hne) S c e hne' hm'
    let oldEar := dartEquiv G a.fst b.fst hne hm (some (some (R.rotate a)))
    let d := dartEquiv (addedGraph G a.fst b.fst hne) c.fst e.fst hne' hm' (some (some oldEar))
    T.face (T.face (T.face d)) = d := by
  classical
  let H := addedGraph G a.fst b.fst hne
  let S := addEdge G R a b hne hm
  let E := dartEquiv G a.fst b.fst hne hm
  have hsep := added_ear_forward_separate G R a b hne hm hpath
  dsimp only at hsep
  have hear : S.face.SameCycle (E none) (E (some (some (R.rotate a)))) := by
    have hh : S.face.SameCycle (E none) (S.face (E none)) :=
      Equiv.Perm.SameCycle.rfl.apply_right
    simpa only [S, E, added_face_reverse] using hh
  have hout : ¬S.face.SameCycle c.symm (E (some (some (R.rotate a)))) := by
    intro hh
    exact hsep (hear.trans ((hcorner.trans hh).symm))
  exact added_ear_preserves_triangle H S c e hne' hm' hnext _ hout
    (added_ear_triangle G R a b hne hm hpath)

end JSP512Probe.EdgeInsertion
