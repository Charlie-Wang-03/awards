import JSP000404Research.ResidualSecondLayerTripleCanonical
import Mathlib.Tactic

/-!
# Fin-3 Q/T/T/T block deficiency

At n=3 every second-layer projected-loss block is a Hamming radius-one ball
in the Boolean 3-cube.  In a saturated Q/T/T/T configuration the four centres
are the common completion word and its three one-coordinate neighbours.
Consequently the union of all four enlarged blocks is exactly the 3-cube
minus the triple antipode, hence has cardinality seven while total dyadic
demand is eight.
-/

namespace JSP000404Research
namespace OrderedEdgeColoring

theorem QTTT_fin3_four_blocks_union_eq_univ_erase_antipode
    {V : Type*} [LinearOrder V] [Fintype V]
    (C : OrderedEdgeColoring V 4)
    (exponent : V → ℕ)
    {s x y z : V}
    (hsLoss : s ∈ projectedLossVertices C exponent)
    (hxLoss : x ∈ projectedLossVertices C exponent)
    (hyLoss : y ∈ projectedLossVertices C exponent)
    (hzLoss : z ∈ projectedLossVertices C exponent)
    (hsSecond : exponent s = 1)
    (hxSecond : exponent x = 1)
    (hySecond : exponent y = 1)
    (hzSecond : exponent z = 1)
    {word : Fin 3 → Bool}
    {cx cy cz : Fin 3}
    (hcxy : cx ≠ cy)
    (hcxz : cx ≠ cz)
    (hcyz : cy ≠ cz)
    (hsQ : word ∈ retainedCompletionWords C s)
    (hxT : word ∈ translatedCompletionWords C x cx)
    (hyT : word ∈ translatedCompletionWords C y cy)
    (hzT : word ∈ translatedCompletionWords C z cz) :
    (((enlargedProjectedCandidateBlock C exponent s ∪
        enlargedProjectedCandidateBlock C exponent x) ∪
        enlargedProjectedCandidateBlock C exponent y) ∪
        enlargedProjectedCandidateBlock C exponent z)
      =
    (Finset.univ : Finset (Fin 3 → Bool)).erase
      (tripleFlipBoolWord word cx cy cz) := by
  classical
  let anti := tripleFlipBoolWord word cx cy cz
  have hthree :=
    QTT_fin3_three_blocks_union_eq_univ_erase_antipode
      C exponent
      hsLoss hxLoss hyLoss
      hsSecond hxSecond hySecond
      hcxy hcxz hcyz hsQ hxT hyT
  have hout :=
    QTTT_fin3_antipode_outside_four_blocks
      C exponent
      hsLoss hxLoss hyLoss hzLoss
      hsSecond hxSecond hySecond hzSecond
      hcxy hcxz hcyz hsQ hxT hyT hzT
  ext q
  constructor
  · intro hq
    have hqNe : q ≠ anti := by
      intro hqa
      subst q
      rcases Finset.mem_union.mp hq with hthreeMem | hzMem
      · rw [hthree] at hthreeMem
        exact (Finset.mem_erase.mp hthreeMem).1 rfl
      · exact hout.2.2.2 hzMem
    simp [anti,hqNe]
  · intro hq
    apply Finset.mem_union_left
    rw [hthree]
    simpa [anti] using hq

theorem QTTT_fin3_four_blocks_union_card_eq_seven
    {V : Type*} [LinearOrder V] [Fintype V]
    (C : OrderedEdgeColoring V 4)
    (exponent : V → ℕ)
    {s x y z : V}
    (hsLoss : s ∈ projectedLossVertices C exponent)
    (hxLoss : x ∈ projectedLossVertices C exponent)
    (hyLoss : y ∈ projectedLossVertices C exponent)
    (hzLoss : z ∈ projectedLossVertices C exponent)
    (hsSecond : exponent s = 1)
    (hxSecond : exponent x = 1)
    (hySecond : exponent y = 1)
    (hzSecond : exponent z = 1)
    {word : Fin 3 → Bool}
    {cx cy cz : Fin 3}
    (hcxy : cx ≠ cy)
    (hcxz : cx ≠ cz)
    (hcyz : cy ≠ cz)
    (hsQ : word ∈ retainedCompletionWords C s)
    (hxT : word ∈ translatedCompletionWords C x cx)
    (hyT : word ∈ translatedCompletionWords C y cy)
    (hzT : word ∈ translatedCompletionWords C z cz) :
    ((((enlargedProjectedCandidateBlock C exponent s ∪
        enlargedProjectedCandidateBlock C exponent x) ∪
        enlargedProjectedCandidateBlock C exponent y) ∪
        enlargedProjectedCandidateBlock C exponent z).card) = 7 := by
  rw [QTTT_fin3_four_blocks_union_eq_univ_erase_antipode
    C exponent
    hsLoss hxLoss hyLoss hzLoss
    hsSecond hxSecond hySecond hzSecond
    hcxy hcxz hcyz hsQ hxT hyT hzT]
  simp

theorem QTTT_fin3_four_vertices_blockDeficient
    {V : Type*} [LinearOrder V] [Fintype V]
    (C : OrderedEdgeColoring V 4)
    (exponent : V → ℕ)
    {s x y z : V}
    (hsx : s ≠ x) (hsy : s ≠ y) (hsz : s ≠ z)
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (hsLoss : s ∈ projectedLossVertices C exponent)
    (hxLoss : x ∈ projectedLossVertices C exponent)
    (hyLoss : y ∈ projectedLossVertices C exponent)
    (hzLoss : z ∈ projectedLossVertices C exponent)
    (hsSecond : exponent s = 1)
    (hxSecond : exponent x = 1)
    (hySecond : exponent y = 1)
    (hzSecond : exponent z = 1)
    {word : Fin 3 → Bool}
    {cx cy cz : Fin 3}
    (hcxy : cx ≠ cy)
    (hcxz : cx ≠ cz)
    (hcyz : cy ≠ cz)
    (hsQ : word ∈ retainedCompletionWords C s)
    (hxT : word ∈ translatedCompletionWords C x cx)
    (hyT : word ∈ translatedCompletionWords C y cy)
    (hzT : word ∈ translatedCompletionWords C z cz) :
    BlockDeficient
      (fun v => 2 ^ exponent v)
      (enlargedProjectedCandidateBlock C exponent)
      ({s,x,y,z} : Finset V) := by
  classical
  unfold BlockDeficient
  have hblocks :
      (({s,x,y,z} : Finset V).biUnion
        (enlargedProjectedCandidateBlock C exponent)).card = 7 := by
    have hEq :
        ({s,x,y,z} : Finset V).biUnion
            (enlargedProjectedCandidateBlock C exponent)
          =
        ((enlargedProjectedCandidateBlock C exponent s ∪
          enlargedProjectedCandidateBlock C exponent x) ∪
          enlargedProjectedCandidateBlock C exponent y) ∪
          enlargedProjectedCandidateBlock C exponent z := by
      ext q
      simp [or_assoc, or_left_comm, or_comm]
    rw [hEq]
    exact QTTT_fin3_four_blocks_union_card_eq_seven
      C exponent
      hsLoss hxLoss hyLoss hzLoss
      hsSecond hxSecond hySecond hzSecond
      hcxy hcxz hcyz hsQ hxT hyT hzT
  rw [hblocks]
  have hcard : ({s,x,y,z} : Finset V).card = 4 := by
    simp [hsx,hsy,hsz,hxy,hxz,hyz,
      Ne.symm hsx,Ne.symm hsy,Ne.symm hsz,
      Ne.symm hxy,Ne.symm hxz,Ne.symm hyz]
  have hsum :
      (∑ v ∈ ({s,x,y,z} : Finset V), 2 ^ exponent v) = 8 := by
    simp [hsSecond,hxSecond,hySecond,hzSecond,
      hsx,hsy,hsz,hxy,hxz,hyz,
      Ne.symm hsx,Ne.symm hsy,Ne.symm hsz,
      Ne.symm hxy,Ne.symm hxz,Ne.symm hyz]
  rw [hsum]
  omega

#print axioms QTTT_fin3_four_blocks_union_eq_univ_erase_antipode
#print axioms QTTT_fin3_four_blocks_union_card_eq_seven
#print axioms QTTT_fin3_four_vertices_blockDeficient

end OrderedEdgeColoring
end JSP000404Research
