"""Write the explicit finite data used by the nine-phase Lean argument."""

from pathlib import Path
from check_nine_phase_capacity import indexed_catalog, SLOTS

source = dict(rows=indexed_catalog(), slots=SLOTS)


def vector(values):
    lines = []
    current = '  !['
    for index, value in enumerate(values):
        part = str(value) + (', ' if index < len(values) - 1 else ']')
        if len(current) + len(part) > 98:
            lines.append(current.rstrip())
            current = '    '
        current += part
    lines.append(current)
    return '\n'.join(lines)


text = '''import JSP000404Research.SmallOddWireCapacity

/-!
# Explicit nine-phase row and covering data

The catalog contains the 78 maximal proper partial two-colourings of the nine-cycle.
Its 42 full binary words give two compatible positions per catalog row. All finite
statements below are verified by ordinary kernel reduction.
-/

namespace JSP000404Research.NinePhase

def positiveMask : Fin 78 → ℕ :=
'''
text += vector([row[0] for row in source['rows']]) + '\n\ndef negativeMask : Fin 78 → ℕ :=\n'
text += vector([row[1] for row in source['rows']]) + '\n\ndef slotMask : Fin 42 → ℕ :=\n'
text += vector(source['slots']) + '''

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
'''
Path('JSP000404Research/NinePhaseData.lean').write_text(text, encoding='utf-8', newline='\n')
print('Wrote nine-phase finite data')
