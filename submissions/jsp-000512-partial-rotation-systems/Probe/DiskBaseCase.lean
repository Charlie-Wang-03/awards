import Probe.DiskInstance
import Probe.ListColorExtension

namespace JSP512Probe.RotationSystem
variable {V C : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj] (R : RotationSystem G)

omit [DecidableEq V] [DecidableRel G.Adj] in
/-- A connected simple outer face with a backtracking corner is the isolated
edge base case: there are exactly the two endpoint vertices. -/
theorem disk_backtracking_vertices (outer : G.Dart) (hD : R.IsTriangulatedDisk outer)
    (hback : R.face outer = outer.symm) : ∀ x : V, x = outer.fst ∨ x = outer.snd := by
  have hclose : R.face (R.face outer) = outer := hD.simple _ _
    Equiv.Perm.SameCycle.rfl.apply_right.apply_right Equiv.Perm.SameCycle.rfl
    (by rw [R.face_source,hback]; rfl)
  have hs := R.rotate_fixed_of_face_two_steps outer hclose
  have ht : R.rotate outer.symm = outer.symm := hback
  have step : ∀ a b, G.Adj a b → (a = outer.fst ∨ a = outer.snd) →
      b = outer.fst ∨ b = outer.snd := by
    intro a b hab ha
    rcases ha with rfl | rfl
    · have he := (R.rotate_fixed_iff_unique outer).mp hs ⟨(outer.fst,b),hab⟩ rfl
      exact Or.inr (congrArg (fun d : G.Dart => d.snd) he)
    · have he := (R.rotate_fixed_iff_unique outer.symm).mp ht ⟨(outer.snd,b),hab⟩ rfl
      exact Or.inl (congrArg (fun d : G.Dart => d.snd) he)
  have walk : ∀ {a b}, G.Walk a b → (a = outer.fst ∨ a = outer.snd) →
      b = outer.fst ∨ b = outer.snd := by
    intro a b p
    induction p with
    | nil => exact id
    | cons h _ ih => exact fun ha => ih (step _ _ h ha)
  intro x
  obtain ⟨p⟩ := hD.connected.preconnected outer.fst x
  exact walk p (Or.inl rfl)

omit [DecidableRel G.Adj] in
/-- The two-endpoint disk base case respects arbitrary lists containing two
distinct prescribed endpoint colors. -/
theorem disk_backtracking_coloring [DecidableEq C] (outer : G.Dart)
    (hD : R.IsTriangulatedDisk outer) (hback : R.face outer = outer.symm)
    (L : V → Finset C) (a b : C) (ha : a ∈ L outer.fst) (hb : b ∈ L outer.snd)
    (hab : a ≠ b) :
    ∃ c : G.Coloring C, ListColoring.Respects G L c ∧ c outer.fst = a ∧ c outer.snd = b := by
  let f : V → C := fun x => if x = outer.fst then a else b
  have hf : f outer.fst = a := by simp [f]
  have ht : f outer.snd = b := by simp [f,outer.adj.ne.symm]
  have valid : ∀ {x y}, G.Adj x y → f x ≠ f y := by
    intro x y hxy
    rcases R.disk_backtracking_vertices outer hD hback x with rfl | rfl <;>
      rcases R.disk_backtracking_vertices outer hD hback y with rfl | rfl
    · exact False.elim (G.irrefl hxy)
    · rw [hf,ht]; exact hab
    · rw [hf,ht]; exact hab.symm
    · exact False.elim (G.irrefl hxy)
  refine ⟨SimpleGraph.Coloring.mk f valid,?_,hf,ht⟩
  intro x
  change f x ∈ L x
  rcases R.disk_backtracking_vertices outer hD hback x with rfl | rfl
  · rw [hf]; exact ha
  · rw [ht]; exact hb
end JSP512Probe.RotationSystem
