import Probe.GutnerRotationCore
import Probe.DeletionFaceCounting
import Mathlib.Data.Fin.VecNotation

namespace JSP512Probe.CycleSurgery
variable {α : Type*} [Fintype α] (σ : Equiv.Perm α)

/-- Exact orbit size for a genuine four-cycle. -/
theorem orbitSize_eq_four (x : α) (h₁ : σ x ≠ x)
    (h₂ : σ (σ x) ≠ x) (h₃ : σ (σ (σ x)) ≠ x)
    (h₄ : σ (σ (σ (σ x))) = x) :
    orbitSize σ (Quotient.mk _ x) = 4 := by
  classical
  have horbit : ∀ y, σ.SameCycle y x ↔
      y ∈ ({x, σ x, σ (σ x), σ (σ (σ x))} : Finset α) := by
    intro y
    constructor
    · intro h
      obtain ⟨n, rfl⟩ := h.symm.exists_nat_pow_eq
      clear h
      induction n with
      | zero => simp
      | succ n ih =>
        rw [pow_succ', Equiv.Perm.mul_apply]
        simp only [Finset.mem_insert, Finset.mem_singleton] at ih ⊢
        rcases ih with h | h | h | h
        · exact Or.inr (Or.inl (congrArg σ h))
        · exact Or.inr (Or.inr (Or.inl (congrArg σ h)))
        · exact Or.inr (Or.inr (Or.inr (congrArg σ h)))
        · exact Or.inl ((congrArg σ h).trans h₄)
    · simp only [Finset.mem_insert, Finset.mem_singleton]
      rintro (rfl | rfl | rfl | rfl)
      · exact Equiv.Perm.SameCycle.rfl
      · exact Equiv.Perm.SameCycle.rfl.apply_left
      · exact Equiv.Perm.SameCycle.rfl.apply_left.apply_left
      · exact Equiv.Perm.SameCycle.rfl.apply_left.apply_left.apply_left
  let e := Equiv.subtypeEquivRight (fun y =>
    (show Quotient.mk (Equiv.Perm.SameCycle.setoid σ) y = Quotient.mk _ x ↔
      y ∈ ({x, σ x, σ (σ x), σ (σ (σ x))} : Finset α) from
        Quotient.eq.trans (horbit y)))
  have h₀₁ : x ≠ σ x := h₁.symm
  have h₀₂ : x ≠ σ (σ x) := h₂.symm
  have h₀₃ : x ≠ σ (σ (σ x)) := h₃.symm
  have h₁₂ : σ x ≠ σ (σ x) := fun h => h₁ (σ.injective h).symm
  have h₁₃ : σ x ≠ σ (σ (σ x)) := fun h => h₂ (σ.injective h).symm
  have h₂₃ : σ (σ x) ≠ σ (σ (σ x)) :=
    fun h => h₁ (σ.injective (σ.injective h)).symm
  unfold orbitSize
  rw [Nat.card_congr e]
  rw [Nat.card_eq_fintype_card, Fintype.card_coe]
  simp [h₀₁, h₀₂, h₀₃, h₁₂, h₁₃, h₂₃]

end JSP512Probe.CycleSurgery

namespace JSP512Probe.Gutner

open RotationSystem CycleSurgery

set_option maxRecDepth 100000
set_option maxHeartbeats 0

instance faceSameCycleDecidable :
    DecidableRel (Equiv.Perm.SameCycle rotationSystem.face) :=
  Equiv.Perm.instDecidableRelSameCycle rotationSystem.face

abbrev FaceOrbit := Quotient (Equiv.Perm.SameCycle.setoid rotationSystem.face)

instance faceOrbitDecidableEq : DecidableEq FaceOrbit :=
  Quotient.decidableEq (d := faceSameCycleDecidable)

noncomputable instance faceOrbitFintype : Fintype FaceOrbit :=
  Fintype.ofSurjective (Quotient.mk'' : graph.Dart → FaceOrbit) Quotient.mk''_surjective

/-- One root for each of the eleven quadrilateral facial orbits. -/
def quadRoot : Fin 11 → graph.Dart :=
  ![⟨(0,81), by decide⟩, ⟨(0,11), by decide⟩, ⟨(0,18), by decide⟩,
    ⟨(0,25), by decide⟩, ⟨(0,32), by decide⟩, ⟨(0,39), by decide⟩,
    ⟨(0,46), by decide⟩, ⟨(0,53), by decide⟩, ⟨(0,60), by decide⟩,
    ⟨(0,67), by decide⟩, ⟨(0,74), by decide⟩]


def quadOrbit (i : Fin 11) : FaceOrbit := Quotient.mk _ (quadRoot i)

def quadOrbits : Finset FaceOrbit := Finset.univ.image quadOrbit

/-- The eleven listed roots represent eleven distinct face orbits. -/
theorem quadOrbits_card : quadOrbits.card = 11 := by
  decide +kernel

/-- A facial orbit is one of the listed exceptional orbits exactly when its
three-step return fails. All other facial orbits are triangles. -/
theorem mem_quadOrbits_iff_three_ne (d : graph.Dart) :
    Quotient.mk (Equiv.Perm.SameCycle.setoid rotationSystem.face) d ∈ quadOrbits ↔
      rotationSystem.face (rotationSystem.face (rotationSystem.face d)) ≠ d := by
  decide +kernel

/-- Every face has length three or four. -/
theorem face_three_or_four (d : graph.Dart) :
    rotationSystem.face (rotationSystem.face (rotationSystem.face d)) = d ∨
    rotationSystem.face (rotationSystem.face (rotationSystem.face (rotationSystem.face d))) = d := by
  decide +kernel

/-- No facial orbit has length one or two. -/
theorem face_two_ne (d : graph.Dart) :
    rotationSystem.face (rotationSystem.face d) ≠ d := by
  decide +kernel

/-- Its edge table has exactly 241 undirected edges. -/
theorem graph_edgeFinset_card : graph.edgeFinset.card = 241 := by
  decide +kernel

/-- Structured orbit counting: 146 triangular faces and eleven quadrilateral
faces give 157 facial orbits without enumerating quotient equality pairwise. -/
theorem faceOrbit_card : Fintype.card FaceOrbit = 157 := by
  classical
  have hsize : ∀ q : FaceOrbit, orbitSize rotationSystem.face q =
      if q ∈ quadOrbits then 4 else 3 := by
    intro q
    induction q using Quotient.inductionOn with
    | h d =>
      by_cases hq : Quotient.mk (Equiv.Perm.SameCycle.setoid rotationSystem.face) d ∈ quadOrbits
      · rw [if_pos hq]
        apply orbitSize_eq_four rotationSystem.face d
        · exact rotationSystem.face_ne_self d
        · exact face_two_ne d
        · exact (mem_quadOrbits_iff_three_ne d).mp hq
        · exact (face_three_or_four d).resolve_left ((mem_quadOrbits_iff_three_ne d).mp hq)
      · rw [if_neg hq]
        apply orbitSize_eq_three rotationSystem.face d (rotationSystem.face_ne_self d)
        by_contra hne
        exact hq ((mem_quadOrbits_iff_three_ne d).mpr hne)
  have hsum := sum_orbitSize rotationSystem.face
  have hrewrite :
      (∑ q : FaceOrbit, orbitSize rotationSystem.face q) =
      ∑ q : FaceOrbit, (if q ∈ quadOrbits then 4 else 3) := by
    apply Finset.sum_congr rfl
    intro q _
    exact hsize q
  rw [hrewrite] at hsum
  have heval :
      (∑ q : FaceOrbit, (if q ∈ quadOrbits then 4 else 3)) =
      3 * Fintype.card FaceOrbit + quadOrbits.card := by
    calc
      (∑ q : FaceOrbit, (if q ∈ quadOrbits then 4 else 3)) =
          ∑ q : FaceOrbit, (3 + if q ∈ quadOrbits then 1 else 0) := by
            apply Finset.sum_congr rfl
            intro q _
            by_cases hq : q ∈ quadOrbits <;> simp [hq]
      _ = 3 * Fintype.card FaceOrbit + quadOrbits.card := by
        simp [Finset.sum_add_distrib, Nat.mul_comm]
  rw [heval, quadOrbits_card] at hsum
  rw [SimpleGraph.dart_card_eq_twice_card_edges] at hsum
  rw [graph_edgeFinset_card] at hsum
  omega


theorem faceCount_eq : rotationSystem.faceCount = 157 := by
  unfold RotationSystem.faceCount RotationSystem.FaceOrbit
  rw [Nat.card_eq_fintype_card]
  exact faceOrbit_card

/-- The concrete obstruction graph is connected. -/
theorem graph_connected : graph.Connected := by
  decide +kernel

/-- Its edge table has exactly 241 undirected edges. -/
theorem graph_edge_count : Nat.card graph.edgeSet = 241 := by
  simpa only [SimpleGraph.edgeFinset, Set.toFinset_card] using graph_edgeFinset_card

noncomputable def componentEquivUnit : graph.ConnectedComponent ≃ Unit where
  toFun := fun _ => ()
  invFun := fun _ => graph.connectedComponentMk 0
  left_inv := by
    intro q
    induction q using Quotient.inductionOn with
    | h v =>
      apply Quotient.sound
      exact graph_connected 0 v
  right_inv := by intro u; cases u; rfl


theorem component_count : Nat.card graph.ConnectedComponent = 1 := by
  simpa using Nat.card_congr componentEquivUnit

/-- The finite rotation table satisfies the spherical Euler equation, hence
is genus zero in the exact sense used by the coloring development. -/
theorem rotation_genusZero : rotationSystem.HasGenusZero := by
  have hs : supportSize (G := graph) = 86 := by
    unfold supportSize
    rw [graph_connected.preconnected.support_eq_univ]
    simp
  unfold HasGenusZero eulerDefect
  rw [component_count, hs, graph_edge_count, faceCount_eq]
  norm_num

end JSP512Probe.Gutner
