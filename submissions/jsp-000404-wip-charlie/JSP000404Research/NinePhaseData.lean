import JSP000404Research.SmallOddWireCapacity

/-!
# Explicit nine-phase row and covering data

The catalog contains the 78 maximal proper partial two-colourings of the nine-cycle.
Its 42 full binary words give two compatible positions per catalog row. All finite
statements below are verified by ordinary kernel reduction.
-/

namespace JSP000404Research.NinePhase

def positiveMask : Fin 78 → ℕ :=
  ![170, 340, 169, 340, 169, 338, 165, 338, 165, 330, 162, 328, 149, 330, 146, 328, 146, 324,
    145, 324, 149, 298, 146, 296, 146, 292, 145, 292, 138, 292, 137, 292, 137, 290, 85, 298, 82,
    296, 82, 292, 81, 292, 74, 292, 73, 292, 73, 290, 74, 276, 73, 276, 73, 274, 69, 274, 85,
    170, 81, 164, 73, 164, 73, 162, 73, 148, 73, 146, 69, 146, 41, 148, 41, 146, 37, 146, 37, 138]

def negativeMask : Fin 78 → ℕ :=
  ![340, 170, 340, 169, 338, 169, 338, 165, 330, 165, 328, 162, 330, 149, 328, 146, 324, 146,
    324, 145, 298, 149, 296, 146, 292, 146, 292, 145, 292, 138, 292, 137, 290, 137, 298, 85, 296,
    82, 292, 82, 292, 81, 292, 74, 292, 73, 290, 73, 276, 74, 276, 73, 274, 73, 274, 69, 170, 85,
    164, 81, 164, 73, 162, 73, 148, 73, 146, 73, 146, 69, 148, 41, 146, 41, 146, 37, 138, 37]

def slotMask : Fin 42 → ℕ :=
  ![73, 83, 85, 101, 107, 146, 149, 153, 165, 166, 169, 170, 171, 173, 179, 181, 202, 205, 213,
    214, 219, 292, 297, 298, 306, 309, 330, 332, 338, 340, 341, 342, 345, 346, 358, 362, 365,
    404, 410, 426, 428, 438]

def row (i : Fin 78) (c : Fin 9) : Option Bool :=
  if (positiveMask i).testBit c.val then some true
  else if (negativeMask i).testBit c.val then some false else none

def next (c : Fin 9) : Fin 9 := ⟨(c.val + 1) % 9, Nat.mod_lt _ (by decide)⟩

def LocalValid (r : Fin 9 → Option Bool) : Prop :=
  ∀ c b, r c = some b → r (next c) ≠ some b

instance (r : Fin 9 → Option Bool) : Decidable (LocalValid r) :=
  inferInstanceAs (Decidable (∀ c b, r c = some b → r (next c) ≠ some b))

def Extends (r s : Fin 9 → Option Bool) : Prop :=
  ∀ c b, r c = some b → s c = some b

instance (r s : Fin 9 → Option Bool) : Decidable (Extends r s) :=
  inferInstanceAs (Decidable (∀ c b, r c = some b → s c = some b))

theorem localValid_of_partialValid {r : Fin 9 → Option Bool} (h : OddWire.PartialValid r) :
    LocalValid r := fun c b hc ↦ h c (next c) rfl b hc

def covers (i : Fin 78) (slot : Fin 42) : Bool :=
  decide (slotMask slot &&& positiveMask i = positiveMask i ∧
    slotMask slot &&& negativeMask i = 0)

def Separated (i j : Fin 78) : Prop :=
  positiveMask i &&& negativeMask j ≠ 0 ∨ negativeMask i &&& positiveMask j ≠ 0

instance (i j : Fin 78) : Decidable (Separated i j) :=
  inferInstanceAs (Decidable
    (positiveMask i &&& negativeMask j ≠ 0 ∨ negativeMask i &&& positiveMask j ≠ 0))

set_option maxRecDepth 32768 in
set_option maxHeartbeats 20000000 in
theorem catalog_completion : ∀ r : Fin 9 → Option Bool, LocalValid r →
    ∃ i : Fin 78, Extends r (row i) := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 4000000 in
theorem catalog_coverage : ∀ i : Fin 78,
    ((Finset.univ : Finset (Fin 42)).filter (fun slot ↦ covers i slot = true)).card = 2 := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 4000000 in
theorem separated_iff_rows : ∀ i j : Fin 78, Separated i j ↔
    ∃ c a b, row i c = some a ∧ row j c = some b ∧ a ≠ b := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 4000000 in
theorem separated_disjoint_covers : ∀ i j : Fin 78, Separated i j →
    ∀ slot : Fin 42, covers i slot = true → covers j slot = false := by
  decide +kernel

#print axioms catalog_completion
#print axioms catalog_coverage
#print axioms separated_iff_rows
#print axioms separated_disjoint_covers

end JSP000404Research.NinePhase
