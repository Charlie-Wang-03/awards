import JSP000404Research.ElevenPhaseCNFModel

/-! Exact finite facts about the four weight orbits in the eleven-phase cover. -/

namespace JSP000404Research.ElevenPhase

open scoped BigOperators

def support (i : Fin 198) : Finset (Fin 132) :=
  Finset.univ.filter fun slot ↦ covers i slot = true

def lowGroup : Finset (Fin 132) := Finset.univ.filter fun slot ↦ slotWeight slot = 2
def mediumGroup : Finset (Fin 132) := Finset.univ.filter fun slot ↦ slotWeight slot = 3
def highGroup : Finset (Fin 132) :=
  Finset.univ.image fun i : Fin 22 ↦ slotIndex (highSlots i)
def specialGroup : Finset (Fin 132) :=
  Finset.univ.image fun i : Fin 22 ↦ slotIndex (high341Slots i)
def longGroup : Finset (Fin 198) :=
  Finset.univ.image fun i : Fin 22 ↦ rowIndex (longRows i)

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem group_partition : lowGroup ∪ mediumGroup ∪ highGroup ∪ specialGroup = Finset.univ ∧
    Disjoint lowGroup mediumGroup ∧ Disjoint lowGroup highGroup ∧ Disjoint lowGroup specialGroup ∧
    Disjoint mediumGroup highGroup ∧ Disjoint mediumGroup specialGroup ∧
    Disjoint highGroup specialGroup := by
  decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem group_sizes : lowGroup.card = 22 ∧ mediumGroup.card = 66 ∧ highGroup.card = 22 ∧
    specialGroup.card = 22 ∧ longGroup.card = 22 := by
  decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem group_weights : (∀ slot ∈ lowGroup, slotWeight slot = 2) ∧
    (∀ slot ∈ mediumGroup, slotWeight slot = 3) ∧
    (∀ slot ∈ highGroup, slotWeight slot = 6) ∧
    (∀ slot ∈ specialGroup, slotWeight slot = 6) := by
  decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem coordinates_injective :
    Function.Injective (fun i : Fin 66 ↦ slotIndex (mediumSlots i)) ∧
    Function.Injective (fun i : Fin 22 ↦ slotIndex (highSlots i)) ∧
    Function.Injective (fun i : Fin 22 ↦ slotIndex (high341Slots i)) ∧
    Function.Injective (fun i : Fin 22 ↦ rowIndex (longRows i)) := by
  decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mediumGroup_image : mediumGroup =
    Finset.univ.image (fun i : Fin 66 ↦ slotIndex (mediumSlots i)) := by
  decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem support_low_count : ∀ i : Fin 198,
    (support i ∩ lowGroup).card = if i ∈ longGroup then 6 else 0 := by
  decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem support_special_count : ∀ i : Fin 198,
    (support i ∩ specialGroup).card =
      if (support i ∩ specialGroup).Nonempty then 2 else 0 := by
  decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem support_weight : ∀ i : Fin 198, (∑ slot ∈ support i, slotWeight slot) = 12 := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem total_weight : (∑ slot : Fin 132, slotWeight slot) = 506 := by
  decide +kernel

#print axioms group_partition
#print axioms support_low_count
#print axioms support_special_count
#print axioms support_weight

end JSP000404Research.ElevenPhase
