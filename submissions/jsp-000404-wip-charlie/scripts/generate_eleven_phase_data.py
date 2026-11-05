"""Generate exact eleven-phase row and weighted-cover data for Lean."""
from pathlib import Path


def catalog(q=11):
    result=[]
    for holes in range(1<<q):
        if holes.bit_count()%2!=1:
            continue
        if any(holes>>i&1 and holes>>((i+1)%q)&1 for i in range(q)):
            continue
        occupied=[i for i in range(q) if not holes>>i&1]
        positive=sum(1<<i for position,i in enumerate(occupied) if position%2==0)
        negative=((1<<q)-1)^holes^positive
        result.extend([(positive,negative),(negative,positive)])
    return result


def rotate(mask,q,shift):
    return ((mask<<shift)|(mask>>(q-shift)))&((1<<q)-1)


def orbit(mask,q):
    return {rotate(value,q,shift) for value in (mask,((1<<q)-1)^mask)
            for shift in range(q)}


def vector(values):
    lines=[]
    current='  !['
    for index,value in enumerate(values):
        part=str(value)+(', ' if index<len(values)-1 else ']')
        if len(current)+len(part)>98:
            lines.append(current.rstrip())
            current='    '
        current+=part
    lines.append(current)
    return '\n'.join(lines)


def main():
    rows=catalog()
    weights={word:weight for p,weight in [(293,3),(307,2),(331,3),(333,3),(339,6),(341,6)]
             for word in orbit(p,11)}
    assert len(rows)==198 and len(weights)==132 and sum(weights.values())==506
    slots=sorted(weights)
    assert all(sum(weights[w] for w in slots if w&p==p and w&n==0)==12 for p,n in rows)
    text='''import JSP000404Research.SmallOddWireCapacity

/-!
# Explicit eleven-phase partial rows and weighted covering data

The catalog has 198 maximal proper partial two-colourings of C11. Its weighted 132-word
cover has total weight 506, and each catalog row covers weight exactly twelve.
-/

namespace JSP000404Research.ElevenPhase

def positiveMask : Fin 198 → ℕ :=
'''
    text+=vector([p for p,_ in rows])+'\n\ndef negativeMask : Fin 198 → ℕ :=\n'
    text+=vector([n for _,n in rows])+'\n\ndef slotMask : Fin 132 → ℕ :=\n'
    text+=vector(slots)+'\n\ndef slotWeight : Fin 132 → ℕ :=\n'
    text+=vector([weights[w] for w in slots])+'''

def row (i : Fin 198) (c : Fin 11) : Option Bool :=
  if (positiveMask i).testBit c.val then some true
  else if (negativeMask i).testBit c.val then some false else none

def next (c : Fin 11) : Fin 11 := ⟨(c.val + 1) % 11, Nat.mod_lt _ (by decide)⟩

def LocalValid (r : Fin 11 → Option Bool) : Prop :=
  ∀ c b, r c = some b → r (next c) ≠ some b

instance (r : Fin 11 → Option Bool) : Decidable (LocalValid r) :=
  inferInstanceAs (Decidable (∀ c b, r c = some b → r (next c) ≠ some b))

def Extends (r s : Fin 11 → Option Bool) : Prop :=
  ∀ c b, r c = some b → s c = some b

instance (r s : Fin 11 → Option Bool) : Decidable (Extends r s) :=
  inferInstanceAs (Decidable (∀ c b, r c = some b → s c = some b))

theorem localValid_of_partialValid {r : Fin 11 → Option Bool} (h : OddWire.PartialValid r) :
    LocalValid r := fun c b hc ↦ h c (next c) rfl b hc

def covers (i : Fin 198) (slot : Fin 132) : Bool :=
  decide (slotMask slot &&& positiveMask i = positiveMask i ∧
    slotMask slot &&& negativeMask i = 0)

def Separated (i j : Fin 198) : Prop :=
  positiveMask i &&& negativeMask j ≠ 0 ∨ negativeMask i &&& positiveMask j ≠ 0

instance (i j : Fin 198) : Decidable (Separated i j) :=
  inferInstanceAs (Decidable
    (positiveMask i &&& negativeMask j ≠ 0 ∨ negativeMask i &&& positiveMask j ≠ 0))

end JSP000404Research.ElevenPhase
'''
    path=Path('JSP000404Research/ElevenPhaseData.lean')
    path.write_text(text,encoding='utf-8',newline='\n')
    print('Wrote',path)

if __name__=='__main__':
    main()
