import JSP000404Research.ElevenPhaseCoreLemmas
import JSP000404Research.ElevenPhasePackingLogic

/-! Every forbidden CNF core is one of the kernel-verified incoherent row sets. -/

namespace JSP000404Research.ElevenPhase

def matchesCore3 (core : List ℕ) : Bool :=
  (List.finRange 66).any fun i ↦
    (List.finRange 3).all fun j ↦ decide ((core3 i j).val ∈ core)

def matchesCore5 (core : List ℕ) : Bool :=
  (List.finRange 22).any fun i ↦
    (List.finRange 5).all fun j ↦ decide ((core5 i j).val ∈ core)

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem obstructionSets_classified :
    obstructionSets.all (fun core ↦ matchesCore3 core || matchesCore5 core) = true := by
  decide +kernel

theorem selected_avoids_core3 {V : Type*} [Fintype V] (code : V → Fin 198)
    (phase : V → V → Fin 11)
    (hshared : ∀ v w, v ≠ w → Shared (row (code v)) (row (code w)) (phase v w))
    (hcoherent : Coherent (fun v ↦ row (code v)) phase)
    (i : Fin 66) : ¬∀ j, (decide (∃ v, code v = core3 i j) : Bool) = true := by
  classical
  intro hall
  have hexists (j : Fin 3) : ∃ v, code v = core3 i j := by simpa using hall j
  choose vertex hvertex using hexists
  have hinjective : Function.Injective vertex := by
    intro a b hab
    apply core3_injective i
    rw [← hvertex a, ← hvertex b, hab]
  exact core3_not_coherent code phase hshared hcoherent i vertex hinjective hvertex

theorem selected_avoids_core5 {V : Type*} [Fintype V] (code : V → Fin 198)
    (phase : V → V → Fin 11)
    (hshared : ∀ v w, v ≠ w → Shared (row (code v)) (row (code w)) (phase v w))
    (hcoherent : Coherent (fun v ↦ row (code v)) phase)
    (i : Fin 22) : ¬∀ j, (decide (∃ v, code v = core5 i j) : Bool) = true := by
  classical
  intro hall
  have hexists (j : Fin 5) : ∃ v, code v = core5 i j := by simpa using hall j
  choose vertex hvertex using hexists
  have hinjective : Function.Injective vertex := by
    intro a b hab
    apply core5_injective i
    rw [← hvertex a, ← hvertex b, hab]
  exact core5_not_coherent code phase hshared hcoherent i vertex hinjective hvertex

theorem selected_avoids_obstructionSets {V : Type*} [Fintype V] (code : V → Fin 198)
    (phase : V → V → Fin 11)
    (hshared : ∀ v w, v ≠ w → Shared (row (code v)) (row (code w)) (phase v w))
    (hcoherent : Coherent (fun v ↦ row (code v)) phase) :
    ∀ core ∈ obstructionSets,
      ¬∀ i ∈ core, (decide (∃ v, code v = rowIndex i) : Bool) = true := by
  classical
  intro core hc hall
  have classified := (List.all_eq_true.mp obstructionSets_classified) core hc
  rcases Bool.or_eq_true.mp classified with h3 | h5
  · unfold matchesCore3 at h3
    obtain ⟨i, _, hi⟩ := List.any_eq_true.mp h3
    apply selected_avoids_core3 code phase hshared hcoherent i
    intro j
    have hj := (List.all_eq_true.mp hi) j (List.mem_finRange j)
    have hmem : (core3 i j).val ∈ core := of_decide_eq_true hj
    have h := hall (core3 i j).val hmem
    simpa [rowIndex, Nat.mod_eq_of_lt (core3 i j).isLt] using h
  · unfold matchesCore5 at h5
    obtain ⟨i, _, hi⟩ := List.any_eq_true.mp h5
    apply selected_avoids_core5 code phase hshared hcoherent i
    intro j
    have hj := (List.all_eq_true.mp hi) j (List.mem_finRange j)
    have hmem : (core5 i j).val ∈ core := of_decide_eq_true hj
    have h := hall (core5 i j).val hmem
    simpa [rowIndex, Nat.mod_eq_of_lt (core5 i j).isLt] using h

#print axioms selected_avoids_obstructionSets

end JSP000404Research.ElevenPhase
