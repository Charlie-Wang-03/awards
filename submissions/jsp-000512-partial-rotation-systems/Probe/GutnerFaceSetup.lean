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

end JSP512Probe.Gutner
