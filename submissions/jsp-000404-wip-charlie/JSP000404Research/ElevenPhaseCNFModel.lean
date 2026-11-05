import JSP000404Research.ElevenPhaseData
import JSP000404Research.ElevenPhaseCores
import JSP000404Research.ElevenPhaseLRAT

/-! A structural description of the CNF used in the eleven-phase packing certificate. -/

namespace JSP000404Research.ElevenPhase

deriving instance DecidableEq for Sat.Literal

instance : DecidableEq Sat.Clause := inferInstanceAs (DecidableEq (List Sat.Literal))

def longRows : Fin 22 → ℕ :=
  ![88, 89, 122, 123, 134, 135, 138, 139, 140, 141, 142, 143, 176, 177, 188, 189, 192, 193, 194,
    195, 196, 197]

def mediumSlots : Fin 66 → ℕ :=
  ![0, 1, 3, 4, 5, 8, 9, 14, 16, 18, 19, 20, 21, 23, 26, 27, 28, 30, 32, 41, 42, 44, 46, 47, 49,
    51, 56, 57, 60, 61, 62, 64, 65, 66, 67, 69, 70, 71, 74, 75, 80, 82, 84, 85, 87, 89, 90, 99,
    101, 103, 104, 105, 108, 110, 111, 112, 113, 115, 117, 122, 123, 126, 127, 128, 130, 131]

def highSlots : Fin 22 → ℕ :=
  ![6, 11, 15, 24, 31, 34, 39, 43, 50, 54, 59, 72, 77, 81, 88, 92, 97, 100, 107, 116, 120, 125]

def high341Slots : Fin 22 → ℕ :=
  ![7, 22, 29, 33, 35, 36, 37, 38, 40, 45, 58, 73, 86, 91, 93, 94, 95, 96, 98, 102, 109, 124]

def obstructionSets : List (List ℕ) :=
  [
    [0, 50, 165],
    [1, 51, 164],
    [2, 48, 82],
    [3, 49, 83],
    [4, 80, 130],
    [5, 81, 131],
    [6, 128, 184],
    [7, 129, 185],
    [8, 105, 182],
    [9, 104, 183],
    [10, 24, 101, 111, 159],
    [10, 28, 177],
    [10, 99, 188],
    [11, 25, 100, 110, 158],
    [11, 29, 176],
    [11, 98, 189],
    [12, 99, 159],
    [13, 98, 158],
    [18, 36, 44, 155, 165],
    [18, 50, 88],
    [18, 123, 153],
    [19, 37, 45, 154, 164],
    [19, 51, 89],
    [19, 122, 152],
    [20, 36, 153],
    [21, 37, 152],
    [22, 32, 177],
    [22, 34, 62],
    [22, 60, 115, 131, 179],
    [23, 33, 176],
    [23, 35, 63],
    [23, 61, 114, 130, 178],
    [24, 32, 48, 62, 74],
    [25, 33, 49, 63, 75],
    [28, 70, 119, 137, 183],
    [28, 111, 145],
    [29, 71, 118, 136, 182],
    [29, 110, 144],
    [32, 82, 142],
    [33, 83, 143],
    [36, 125, 192],
    [37, 124, 193],
    [40, 54, 88],
    [40, 56, 102],
    [40, 92, 100, 169, 185],
    [41, 55, 89],
    [41, 57, 103],
    [41, 93, 101, 168, 184],
    [44, 54, 80, 102, 118],
    [45, 55, 81, 103, 119],
    [48, 124, 194],
    [49, 125, 195],
    [50, 98, 114, 173, 191],
    [51, 99, 115, 172, 190],
    [54, 130, 196],
    [55, 131, 197],
    [60, 68, 104, 146, 154],
    [61, 69, 105, 147, 155],
    [62, 135, 179],
    [63, 134, 178],
    [68, 86, 142],
    [68, 90, 156],
    [69, 87, 143],
    [69, 91, 157],
    [70, 82, 124, 152, 168],
    [71, 83, 125, 153, 169],
    [74, 86, 128, 156, 172],
    [75, 87, 129, 157, 173],
    [80, 139, 178],
    [81, 138, 179],
    [86, 141, 184],
    [87, 140, 185],
    [92, 102, 189],
    [92, 129, 192],
    [93, 103, 188],
    [93, 128, 193],
    [104, 137, 194],
    [105, 136, 195],
    [110, 136, 196],
    [111, 137, 197],
    [122, 146, 156],
    [123, 147, 157],
    [134, 147, 182],
    [135, 146, 183],
    [138, 159, 190],
    [139, 158, 191],
    [140, 165, 191],
    [141, 164, 190]
  ]

def rowIndex (n : ℕ) : Fin 198 := ⟨n % 198, Nat.mod_lt _ (by decide)⟩
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
