import JSP000404Research.ElevenPhaseData
import JSP000404Research.ElevenPhaseOrder

/-!
# Finite triple-coherence obstructions

Each three-row core is already incoherent. For every five-row core, the three triangles
sharing its first pair impose incompatible phase choices on that pair.
-/

namespace JSP000404Research.ElevenPhase

def before (r : Fin 11 → Option Bool) (phase : Fin 11) : Bool :=
  r phase == some (decide ((phase.val : ℤ) % 2 = 0))

def Shared (r s : Fin 11 → Option Bool) (phase : Fin 11) : Prop :=
  (r phase = some true ∧ s phase = some false) ∨
    (r phase = some false ∧ s phase = some true)

instance (r s : Fin 11 → Option Bool) (phase : Fin 11) : Decidable (Shared r s phase) :=
  inferInstanceAs (Decidable
    ((r phase = some true ∧ s phase = some false) ∨
      (r phase = some false ∧ s phase = some true)))

def Coherent {V : Type*} (r : V → Fin 11 → Option Bool) (phase : V → V → Fin 11) : Prop :=
  ∀ a b c, a ≠ b → a ≠ c → b ≠ c →
    OrderedPhases (phase a b).val (phase a c).val (phase b c).val
      (before (r a) (phase a b)) (before (r a) (phase a c)) (before (r b) (phase b c))

def core3 : Fin 66 → Fin 3 → Fin 198 :=
  ![
    ![0, 50, 165],
    ![1, 51, 164],
    ![2, 48, 82],
    ![3, 49, 83],
    ![4, 80, 130],
    ![5, 81, 131],
    ![6, 128, 184],
    ![7, 129, 185],
    ![8, 105, 182],
    ![9, 104, 183],
    ![10, 28, 177],
    ![10, 99, 188],
    ![11, 29, 176],
    ![11, 98, 189],
    ![12, 99, 159],
    ![13, 98, 158],
    ![18, 50, 88],
    ![18, 123, 153],
    ![19, 51, 89],
    ![19, 122, 152],
    ![20, 36, 153],
    ![21, 37, 152],
    ![22, 32, 177],
    ![22, 34, 62],
    ![23, 33, 176],
    ![23, 35, 63],
    ![28, 111, 145],
    ![29, 110, 144],
    ![32, 82, 142],
    ![33, 83, 143],
    ![36, 125, 192],
    ![37, 124, 193],
    ![40, 54, 88],
    ![40, 56, 102],
    ![41, 55, 89],
    ![41, 57, 103],
    ![48, 124, 194],
    ![49, 125, 195],
    ![54, 130, 196],
    ![55, 131, 197],
    ![62, 135, 179],
    ![63, 134, 178],
    ![68, 86, 142],
    ![68, 90, 156],
    ![69, 87, 143],
    ![69, 91, 157],
    ![80, 139, 178],
    ![81, 138, 179],
    ![86, 141, 184],
    ![87, 140, 185],
    ![92, 102, 189],
    ![92, 129, 192],
    ![93, 103, 188],
    ![93, 128, 193],
    ![104, 137, 194],
    ![105, 136, 195],
    ![110, 136, 196],
    ![111, 137, 197],
    ![122, 146, 156],
    ![123, 147, 157],
    ![134, 147, 182],
    ![135, 146, 183],
    ![138, 159, 190],
    ![139, 158, 191],
    ![140, 165, 191],
    ![141, 164, 190]
  ]

def core5 : Fin 22 → Fin 5 → Fin 198 :=
  ![
    ![24, 101, 10, 111, 159],
    ![25, 100, 11, 110, 158],
    ![44, 155, 18, 36, 165],
    ![45, 154, 19, 37, 164],
    ![60, 115, 22, 131, 179],
    ![61, 114, 23, 130, 178],
    ![24, 74, 32, 48, 62],
    ![25, 75, 33, 49, 63],
    ![70, 119, 28, 137, 183],
    ![71, 118, 29, 136, 182],
    ![100, 169, 40, 92, 185],
    ![101, 168, 41, 93, 184],
    ![44, 118, 54, 80, 102],
    ![45, 119, 55, 81, 103],
    ![114, 173, 50, 98, 191],
    ![115, 172, 51, 99, 190],
    ![60, 154, 68, 104, 146],
    ![61, 155, 69, 105, 147],
    ![70, 168, 82, 124, 152],
    ![71, 169, 83, 125, 153],
    ![74, 172, 86, 128, 156],
    ![75, 173, 87, 129, 157]
  ]

def ValidTriple (a b c : Fin 198) (ab ac bc : Fin 11) : Prop :=
  Shared (row a) (row b) ab ∧ Shared (row a) (row c) ac ∧ Shared (row b) (row c) bc ∧
    OrderedPhases ab.val ac.val bc.val
      (before (row a) ab) (before (row a) ac) (before (row b) bc)

instance (a b c : Fin 198) (ab ac bc : Fin 11) : Decidable (ValidTriple a b c ab ac bc) :=
  inferInstanceAs (Decidable
    (Shared (row a) (row b) ab ∧ Shared (row a) (row c) ac ∧ Shared (row b) (row c) bc ∧
      OrderedPhases ab.val ac.val bc.val
        (before (row a) ab) (before (row a) ac) (before (row b) bc)))

def AllowedPair (a b c : Fin 198) (ab : Fin 11) : Prop :=
  ∃ ac bc, ValidTriple a b c ab ac bc

instance (a b c : Fin 198) (ab : Fin 11) : Decidable (AllowedPair a b c ab) :=
  inferInstanceAs (Decidable (∃ ac bc, ValidTriple a b c ab ac bc))

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem core3_impossible : ∀ i : Fin 66, ∀ ab ac bc : Fin 11,
    ¬ValidTriple (core3 i 0) (core3 i 1) (core3 i 2) ab ac bc := by
  decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem core5_impossible : ∀ i : Fin 22, ∀ ab : Fin 11,
    ¬(AllowedPair (core5 i 0) (core5 i 1) (core5 i 2) ab ∧
      AllowedPair (core5 i 0) (core5 i 1) (core5 i 3) ab ∧
      AllowedPair (core5 i 0) (core5 i 1) (core5 i 4) ab) := by
  decide +kernel

#print axioms core3_impossible
#print axioms core5_impossible

end JSP000404Research.ElevenPhase
