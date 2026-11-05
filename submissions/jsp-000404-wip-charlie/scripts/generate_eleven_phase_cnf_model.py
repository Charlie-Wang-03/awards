"""Emit a structural Lean description of the checked eleven-phase CNF."""
from itertools import combinations
from pathlib import Path
from generate_eleven_phase_data import catalog,orbit
from generate_eleven_phase_cores import images


def vector(values):
    rows=[]
    line='  !['
    for i,value in enumerate(values):
        part=str(value)+(', ' if i<len(values)-1 else ']')
        if len(line)+len(part)>98:
            rows.append(line.rstrip())
            line='    '
        line+=part
    rows.append(line)
    return '\n'.join(rows)


def main():
    rows=catalog()
    weights={w:weight for p,weight in [(293,3),(307,2),(331,3),(333,3),(339,6),(341,6)]
             for w in orbit(p,11)}
    slots=sorted(weights)
    medium=sorted(set().union(*(orbit(p,11) for p in (293,331,333))))
    high=sorted(orbit(339,11))
    high341=sorted(orbit(341,11))
    long=[i for i,(p,n) in enumerate(rows) if (p|n).bit_count()==6]
    cores=sorted(images((11,29,176))|images((6,128,184))|images((24,32,48,62,74)))
    assert len(cores)==88 and len(long)==22
    text='''import JSP000404Research.ElevenPhaseData
import JSP000404Research.ElevenPhaseCores
import JSP000404Research.ElevenPhaseLRAT

/-! A structural description of the CNF used in the eleven-phase packing certificate. -/

namespace JSP000404Research.ElevenPhase

deriving instance DecidableEq for Sat.Literal

instance : DecidableEq Sat.Clause := inferInstanceAs (DecidableEq (List Sat.Literal))

def longRows : Fin 22 → ℕ :=
'''
    text+=vector(long)+'\n\ndef mediumSlots : Fin 66 → ℕ :=\n'
    text+=vector([slots.index(x) for x in medium])+'\n\ndef highSlots : Fin 22 → ℕ :=\n'
    text+=vector([slots.index(x) for x in high])+'\n\ndef high341Slots : Fin 22 → ℕ :=\n'
    text+=vector([slots.index(x) for x in high341])+'\n\ndef obstructionSets : List (List ℕ) :=\n  [\n'
    text+=',\n'.join('    ['+', '.join(map(str,core))+']' for core in cores)+'\n  ]\n\n'
    text+='''def rowIndex (n : ℕ) : Fin 198 := ⟨n % 198, Nat.mod_lt _ (by decide)⟩
def slotIndex (n : ℕ) : Fin 132 := ⟨n % 132, Nat.mod_lt _ (by decide)⟩
def longIndex (n : ℕ) : ℕ := longRows ⟨n % 22, Nat.mod_lt _ (by decide)⟩
def mediumSlot (n : ℕ) : ℕ := mediumSlots ⟨n % 66, Nat.mod_lt _ (by decide)⟩
def highSlot (n : ℕ) : ℕ := highSlots ⟨n % 22, Nat.mod_lt _ (by decide)⟩
def high341Slot (n : ℕ) : ℕ := high341Slots ⟨n % 22, Nat.mod_lt _ (by decide)⟩

def negative (n : ℕ) : Sat.Literal := .neg n
def positive (n : ℕ) : Sat.Literal := .pos n

def conflictClauses : Sat.Fmla :=
  (List.range 198).flatMap fun i ↦
    ((List.range 198).filter (fun j ↦ i < j ∧ ¬Separated (rowIndex i) (rowIndex j))).map
      (fun j ↦ [negative i, negative j])

def coreClauses : Sat.Fmla :=
  obstructionSets.map fun core ↦ core.map negative

def coverers (slot : ℕ) : List ℕ :=
  (List.range 198).filter fun i ↦ covers (rowIndex i) (slotIndex slot)

def coveredClause (slot : ℕ) : Sat.Clause := (coverers slot).map positive

def high341Clauses : Sat.Fmla :=
  (List.range 22).map fun i ↦ coveredClause (high341Slot i)

def longAtLeastThreeClauses : Sat.Fmla :=
  (List.range 22).flatMap fun i ↦
    ((List.range 22).filter fun j ↦ i < j).map fun j ↦
      ((List.range 22).filter fun k ↦ k ≠ i ∧ k ≠ j).map fun k ↦ positive (longIndex k)

def sequentialClauses (input : ℕ → ℕ) (offset count limit : ℕ) : Sat.Fmla :=
  ((List.range count).flatMap fun i ↦
    (List.range (limit + 1)).flatMap fun j ↦
      (if i = 0 then [] else
        [[negative (offset + (i - 1) * (limit + 1) + j),
          positive (offset + i * (limit + 1) + j)]]) ++
      (if j = 0 then [[negative (input i), positive (offset + i * (limit + 1))]]
       else if i = 0 then [] else
        [[negative (input i), negative (offset + (i - 1) * (limit + 1) + j - 1),
          positive (offset + i * (limit + 1) + j)]])) ++
    [[negative (offset + (count - 1) * (limit + 1) + limit)]]

def missingSlot (i : ℕ) : ℕ := if i < 66 then mediumSlot i else highSlot (i - 66)

def missingClauses : Sat.Fmla :=
  (List.range 88).map fun i ↦ positive (286 + i) :: coveredClause (missingSlot i)

def crossClauses : Sat.Fmla :=
  (List.range 22).flatMap fun h ↦
    (List.range 66).map fun m ↦ [negative (286 + 66 + h), negative (286 + m)]

def modelFormula : Sat.Fmla :=
  conflictClauses ++ coreClauses ++ high341Clauses ++ longAtLeastThreeClauses ++
    sequentialClauses longIndex 198 22 3 ++ missingClauses ++
    sequentialClauses (fun i ↦ 286 + i) 374 66 2 ++
    sequentialClauses (fun i ↦ 286 + 66 + i) 572 22 1 ++ crossClauses

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem modelFormula_eq : modelFormula = packing_refutation.formula := by
  decide +kernel

#print axioms modelFormula_eq

end JSP000404Research.ElevenPhase
'''
    path=Path('JSP000404Research/ElevenPhaseCNFModel.lean')
    path.write_text(text,encoding='utf-8',newline='\n')
    assert all(len(line)<=100 for line in text.splitlines()),path
    print('Wrote',path)

if __name__=='__main__':
    main()
