"""Generate and independently check the small eleven-phase coherence obstructions."""
from itertools import combinations,permutations,product
from pathlib import Path
from generate_eleven_phase_data import catalog,rotate


Q=11
ROWS=catalog()
INDEX={r:i for i,r in enumerate(ROWS)}
FULL=(1<<Q)-1


def shared(left,right):
    bits=(left[0]&right[1])|(left[1]&right[0])
    return [i for i in range(Q) if bits>>i&1]


def coherent(rows,phases):
    times=dict(zip(combinations(range(3),2),phases))
    before={}
    for (a,b),phase in times.items():
        before[a,b]=bool(rows[a][0]>>phase&1)==(phase%2==0)
        before[b,a]=not before[a,b]
    for i,j,k in permutations(range(3)):
        if before[i,j] and before[j,k] and before[i,k]:
            a,b,c=[times[tuple(sorted(edge))] for edge in [(i,j),(i,k),(j,k)]]
            return min(a,c)<=b<=max(a,c)
    return False


def table(triple):
    triple=tuple(sorted(triple))
    edges=list(combinations(triple,2))
    family=[ROWS[i] for i in triple]
    masks=[0,0,0]
    for values in product(*(shared(ROWS[i],ROWS[j]) for i,j in edges)):
        if coherent(family,values):
            for k,v in enumerate(values):
                masks[k]|=1<<v
    return masks


def witness(core):
    core=tuple(sorted(core))
    if len(core)==3:
        return core if not any(table(core)) else None
    for pair in combinations(core,2):
        allowed=FULL
        for vertex in core:
            if vertex in pair:
                continue
            triple=tuple(sorted((*pair,vertex)))
            allowed &= table(triple)[list(combinations(triple,2)).index(pair)]
        if not allowed:
            return (*pair,*(v for v in core if v not in pair))
    return None


def images(core):
    def reflect(mask):
        return sum(((mask>>i)&1)<<((-i)%Q) for i in range(Q))
    result=set()
    for reflection,shift,flip in product((False,True),range(Q),(False,True)):
        image=[]
        for i in core:
            p,n=ROWS[i]
            if reflection:
                p,n=reflect(p),reflect(n)
            p,n=rotate(p,Q,shift),rotate(n,Q,shift)
            if flip:
                p,n=n,p
            image.append(INDEX[p,n])
        found=witness(image)
        if found is not None:
            result.add(tuple(sorted(found)))
    return result


def vector(rows):
    return '  ![\n'+',\n'.join('    !['+', '.join(map(str,row))+']' for row in rows)+'\n  ]'


def main():
    triples=sorted(images((11,29,176))|images((6,128,184)))
    five=[witness(core) for core in sorted(images((24,32,48,62,74)))]
    assert len(triples)==66 and len(five)==22 and all(five)
    text='''import JSP000404Research.ElevenPhaseData
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
'''
    text+=vector(triples)+'\n\ndef core5 : Fin 22 → Fin 5 → Fin 198 :=\n'+vector(five)+'''

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
'''
    path=Path('JSP000404Research/ElevenPhaseCores.lean')
    path.write_text(text,encoding='utf-8',newline='\n')
    assert all(len(line)<=100 for line in text.splitlines()),path
    print('Wrote',path,'with',len(triples),'three-row and',len(five),'five-row cores')

if __name__=='__main__':
    main()
