import JSP000404Research.NinePhaseData
import JSP000404Research.NinePhaseOrder

/-!
# The five-row obstruction to a saturated nine-phase cover

Seven pair phases suffice. Six are forced; the remaining phase belongs to {2,5,8}.
Three actual triangle-order conditions exclude its three possibilities. Both common
polarities are checked against the same explicit catalog data.
-/

namespace JSP000404Research.NinePhase

def before (r : Fin 9 → Option Bool) (phase : Fin 9) : Bool :=
  r phase == some (decide ((phase.val : ℤ) % 2 = 0))

def Shared (r s : Fin 9 → Option Bool) (phase : Fin 9) : Prop :=
  (r phase = some true ∧ s phase = some false) ∨
    (r phase = some false ∧ s phase = some true)

instance (r s : Fin 9 → Option Bool) (phase : Fin 9) : Decidable (Shared r s phase) :=
  inferInstanceAs (Decidable
    ((r phase = some true ∧ s phase = some false) ∨
      (r phase = some false ∧ s phase = some true)))

def Coherent {V : Type*} (r : V → Fin 9 → Option Bool) (phase : V → V → Fin 9) : Prop :=
  ∀ a b c, a ≠ b → a ≠ c → b ≠ c →
    OrderedPhases (phase a b).val (phase a c).val (phase b c).val
      (before (r a) (phase a b)) (before (r a) (phase a c)) (before (r b) (phase b c))

def coreCode (flip : Bool) : Fin 5 → Fin 78 :=
  if flip then ![24, 55, 71, 10, 45] else ![25, 54, 70, 11, 44]

private theorem core_phase01 : ∀ flip c,
    Shared (row (coreCode flip 0)) (row (coreCode flip 1)) c → c = 8 := by decide

private theorem core_phase02 : ∀ flip c,
    Shared (row (coreCode flip 0)) (row (coreCode flip 2)) c → c = 2 := by decide

private theorem core_phase03 : ∀ flip c,
    Shared (row (coreCode flip 0)) (row (coreCode flip 3)) c → c = 5 := by decide

private theorem core_phase14 : ∀ flip c,
    Shared (row (coreCode flip 1)) (row (coreCode flip 4)) c → c = 2 := by decide

private theorem core_phase24 : ∀ flip c,
    Shared (row (coreCode flip 2)) (row (coreCode flip 4)) c → c = 5 := by decide

private theorem core_phase34 : ∀ flip c,
    Shared (row (coreCode flip 3)) (row (coreCode flip 4)) c → c = 8 := by decide

private theorem core_phase04 : ∀ flip c,
    Shared (row (coreCode flip 0)) (row (coreCode flip 4)) c → c = 2 ∨ c = 5 ∨ c = 8 := by
  decide

private theorem core_bad_two : ∀ flip,
    ¬OrderedPhases 5 2 8 (before (row (coreCode flip 0)) 5)
      (before (row (coreCode flip 0)) 2) (before (row (coreCode flip 3)) 8) := by decide

private theorem core_bad_five : ∀ flip,
    ¬OrderedPhases 8 5 2 (before (row (coreCode flip 0)) 8)
      (before (row (coreCode flip 0)) 5) (before (row (coreCode flip 1)) 2) := by decide

private theorem core_bad_eight : ∀ flip,
    ¬OrderedPhases 2 8 5 (before (row (coreCode flip 0)) 2)
      (before (row (coreCode flip 0)) 8) (before (row (coreCode flip 2)) 5) := by decide

theorem core_not_coherent (flip : Bool) (phase : Fin 5 → Fin 5 → Fin 9)
    (hshared : ∀ i j, i ≠ j →
      Shared (row (coreCode flip i)) (row (coreCode flip j)) (phase i j))
    (hcoherent : Coherent (fun i ↦ row (coreCode flip i)) phase) : False := by
  have h01 := core_phase01 flip _ (hshared 0 1 (by decide))
  have h02 := core_phase02 flip _ (hshared 0 2 (by decide))
  have h03 := core_phase03 flip _ (hshared 0 3 (by decide))
  have h14 := core_phase14 flip _ (hshared 1 4 (by decide))
  have h24 := core_phase24 flip _ (hshared 2 4 (by decide))
  have h34 := core_phase34 flip _ (hshared 3 4 (by decide))
  rcases core_phase04 flip _ (hshared 0 4 (by decide)) with h04 | h04 | h04
  · have h := hcoherent 0 3 4 (by decide) (by decide) (by decide)
    rw [h03, h04, h34] at h
    exact core_bad_two flip h
  · have h := hcoherent 0 1 4 (by decide) (by decide) (by decide)
    rw [h01, h04, h14] at h
    exact core_bad_five flip h
  · have h := hcoherent 0 2 4 (by decide) (by decide) (by decide)
    rw [h02, h04, h24] at h
    exact core_bad_eight flip h

#print axioms core_not_coherent

end JSP000404Research.NinePhase
