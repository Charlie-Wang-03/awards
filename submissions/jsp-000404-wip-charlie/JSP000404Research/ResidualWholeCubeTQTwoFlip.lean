import JSP000404Research.ResidualWholeCubeSecondCoordinateCollision
import JSP000404Research.ResidualPairFlipBlocker
import JSP000404Research.ResidualTranslatedOverlapFreeInheritance
import Mathlib.Tactic

/-!
# Two-flip semantics of the T/Q whole-cube augmentation

Let (s,v,c) be a whole-cube Q/T pair, so T_c(v)=Q_s.  Suppose an augmenting
word y lies in a second translated slice T_d(v), d!=c, and simultaneously in
the base cube Q_w.

Writing x=flip_d(y), we have x in Q_v.  Therefore flip_c(x) belongs to
T_c(v)=Q_s.  Equivalently,

  y in Q_w,
  flip_c(flip_d(y)) in Q_s.

Since c and d are both active at v and the whole-cube pair has equal retained
palettes, both are also active at s.  Comparing the Q_w base word y with the
double-flipped Q_s word forces Q_w, whenever it activates either c or d, to
carry the opposite retained bit at that coordinate from s.

The theorem below packages the exact two-flip relation and a basic active-bit
separation consequence.
-/

namespace JSP000404Research
namespace OrderedEdgeColoring

theorem wholeCube_TQ_gives_twoFlip_into_partner_cube
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    {s v w : V} {c d : Fin n}
    (hcV : c ∈ retainedActive C v)
    (hdV : d ∈ retainedActive C v)
    (hdc : d ≠ c)
    (hwhole : WholeCubeQTPair C s v c)
    {word : Fin n → Bool}
    (hvT : word ∈ translatedCompletionWords C v d)
    (hwQ : word ∈ retainedCompletionWords C w) :
    word ∈ retainedCompletionWords C w ∧
    flipBoolWordAt (flipBoolWordAt word d) c ∈
      retainedCompletionWords C s ∧
    c ∈ retainedActive C s ∧
    d ∈ retainedActive C s := by
  rcases hwhole with ⟨hactiveEq,htransEq⟩
  have hbaseV :
      flipBoolWordAt word d ∈ retainedCompletionWords C v :=
    (mem_translatedCompletionWords C v d word).1 hvT
  have hintoTc :
      flipBoolWordAt (flipBoolWordAt word d) c ∈
        translatedCompletionWords C v c := by
    apply (mem_translatedCompletionWords
      C v c (flipBoolWordAt (flipBoolWordAt word d) c)).2
    simpa [flipBoolWordAt_involutive] using hbaseV
  have hsQ :
      flipBoolWordAt (flipBoolWordAt word d) c ∈
        retainedCompletionWords C s := by
    rw [← htransEq]
    exact hintoTc
  have hcS : c ∈ retainedActive C s := by
    rw [← hactiveEq]
    exact hcV
  have hdS : d ∈ retainedActive C s := by
    rw [← hactiveEq]
    exact hdV
  exact ⟨hwQ,hsQ,hcS,hdS⟩

theorem wholeCube_TQ_bit_opposite_at_c_of_active
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    {s v w : V} {c d : Fin n}
    (hcV : c ∈ retainedActive C v)
    (hdV : d ∈ retainedActive C v)
    (hdc : d ≠ c)
    (hwhole : WholeCubeQTPair C s v c)
    {word : Fin n → Bool}
    (hvT : word ∈ translatedCompletionWords C v d)
    (hwQ : word ∈ retainedCompletionWords C w)
    (hcW : c ∈ retainedActive C w) :
    retainedBit C w c = !(retainedBit C s c) := by
  obtain ⟨_,hsQ,hcS,_⟩ :=
    wholeCube_TQ_gives_twoFlip_into_partner_cube
      C hcV hdV hdc hwhole hvT hwQ
  have hwComp :=
    (mem_retainedCompletionWords C w word).1 hwQ
  have hsComp :=
    (mem_retainedCompletionWords C s
      (flipBoolWordAt (flipBoolWordAt word d) c)).1 hsQ
  have hwAt := hwComp c hcW
  have hsAt := hsComp c hcS
  have hdc' : c ≠ d := hdc.symm
  rw [flipBoolWordAt_at,
      flipBoolWordAt_off word hdc'] at hsAt
  rw [hwAt] at hsAt
  exact hsAt.symm

theorem wholeCube_TQ_bit_opposite_at_d_of_active
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    {s v w : V} {c d : Fin n}
    (hcV : c ∈ retainedActive C v)
    (hdV : d ∈ retainedActive C v)
    (hdc : d ≠ c)
    (hwhole : WholeCubeQTPair C s v c)
    {word : Fin n → Bool}
    (hvT : word ∈ translatedCompletionWords C v d)
    (hwQ : word ∈ retainedCompletionWords C w)
    (hdW : d ∈ retainedActive C w) :
    retainedBit C w d = !(retainedBit C s d) := by
  obtain ⟨_,hsQ,_,hdS⟩ :=
    wholeCube_TQ_gives_twoFlip_into_partner_cube
      C hcV hdV hdc hwhole hvT hwQ
  have hwComp :=
    (mem_retainedCompletionWords C w word).1 hwQ
  have hsComp :=
    (mem_retainedCompletionWords C s
      (flipBoolWordAt (flipBoolWordAt word d) c)).1 hsQ
  have hwAt := hwComp d hdW
  have hsAt := hsComp d hdS
  rw [flipBoolWordAt_off _ hdc,
      flipBoolWordAt_at] at hsAt
  rw [hwAt] at hsAt
  exact hsAt.symm

theorem wholeCube_TQ_completion_cubes_disjoint_if_c_active
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    {s v w : V} {c d : Fin n}
    (hcV : c ∈ retainedActive C v)
    (hdV : d ∈ retainedActive C v)
    (hdc : d ≠ c)
    (hwhole : WholeCubeQTPair C s v c)
    {word : Fin n → Bool}
    (hvT : word ∈ translatedCompletionWords C v d)
    (hwQ : word ∈ retainedCompletionWords C w)
    (hcW : c ∈ retainedActive C w) :
    Disjoint
      (retainedCompletionWords C s)
      (retainedCompletionWords C w) := by
  obtain ⟨_,_,hcS,_⟩ :=
    wholeCube_TQ_gives_twoFlip_into_partner_cube
      C hcV hdV hdc hwhole hvT hwQ
  have hbit :=
    wholeCube_TQ_bit_opposite_at_c_of_active
      C hcV hdV hdc hwhole hvT hwQ hcW
  apply completion_disjoint_of_active_bit_ne C hcS hcW
  rw [hbit]
  cases h : retainedBit C s c <;> simp [h]

#print axioms wholeCube_TQ_gives_twoFlip_into_partner_cube
#print axioms wholeCube_TQ_bit_opposite_at_c_of_active
#print axioms wholeCube_TQ_bit_opposite_at_d_of_active

end OrderedEdgeColoring
end JSP000404Research
