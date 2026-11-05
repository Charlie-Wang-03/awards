import JSP000404Research.ElevenPhaseCores

/-! Coherent row families cannot contain any of the certified finite obstructions. -/

namespace JSP000404Research.ElevenPhase

set_option maxRecDepth 16384 in
theorem core3_injective : ∀ i : Fin 66, Function.Injective (core3 i) := by decide +kernel

set_option maxRecDepth 16384 in
theorem core5_injective : ∀ i : Fin 22, Function.Injective (core5 i) := by decide +kernel

theorem validTriple_of_coherent {V : Type*} (code : V → Fin 198)
    (phase : V → V → Fin 11)
    (hshared : ∀ v w, v ≠ w → Shared (row (code v)) (row (code w)) (phase v w))
    (hcoherent : Coherent (fun v ↦ row (code v)) phase)
    {a b c : V} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    ValidTriple (code a) (code b) (code c) (phase a b) (phase a c) (phase b c) :=
  ⟨hshared a b hab, hshared a c hac, hshared b c hbc, hcoherent a b c hab hac hbc⟩

theorem core3_not_coherent {V : Type*} (code : V → Fin 198)
    (phase : V → V → Fin 11)
    (hshared : ∀ v w, v ≠ w → Shared (row (code v)) (row (code w)) (phase v w))
    (hcoherent : Coherent (fun v ↦ row (code v)) phase)
    (i : Fin 66) (vertex : Fin 3 → V) (hinjective : Function.Injective vertex)
    (hcode : ∀ j, code (vertex j) = core3 i j) : False := by
  have h := validTriple_of_coherent code phase hshared hcoherent
    (hinjective.ne (by decide : (0 : Fin 3) ≠ 1))
    (hinjective.ne (by decide : (0 : Fin 3) ≠ 2))
    (hinjective.ne (by decide : (1 : Fin 3) ≠ 2))
  rw [hcode, hcode, hcode] at h
  exact core3_impossible i _ _ _ h

theorem core5_not_coherent {V : Type*} (code : V → Fin 198)
    (phase : V → V → Fin 11)
    (hshared : ∀ v w, v ≠ w → Shared (row (code v)) (row (code w)) (phase v w))
    (hcoherent : Coherent (fun v ↦ row (code v)) phase)
    (i : Fin 22) (vertex : Fin 5 → V) (hinjective : Function.Injective vertex)
    (hcode : ∀ j, code (vertex j) = core5 i j) : False := by
  have hallowed (j : Fin 5) (hj0 : j ≠ 0) (hj1 : j ≠ 1) :
      AllowedPair (core5 i 0) (core5 i 1) (core5 i j) (phase (vertex 0) (vertex 1)) := by
    refine ⟨phase (vertex 0) (vertex j), phase (vertex 1) (vertex j), ?_⟩
    have h := validTriple_of_coherent code phase hshared hcoherent
      (hinjective.ne (by decide : (0 : Fin 5) ≠ 1))
      (hinjective.ne (Ne.symm hj0)) (hinjective.ne (Ne.symm hj1))
    rw [hcode, hcode, hcode] at h
    exact h
  exact core5_impossible i _ ⟨hallowed 2 (by decide) (by decide),
    hallowed 3 (by decide) (by decide), hallowed 4 (by decide) (by decide)⟩

#print axioms core3_not_coherent
#print axioms core5_not_coherent

end JSP000404Research.ElevenPhase
