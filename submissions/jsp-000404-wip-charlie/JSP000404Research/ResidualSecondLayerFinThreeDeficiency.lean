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


/-- Any three of the four n=3 Q/T/T/T blocks have union cardinality seven,
hence are not deficient against total demand six. -/
theorem QTTT_fin3_three_vertex_subsets_not_deficient
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
    ∀ U : Finset V,
      U ⊆ ({s,x,y,z} : Finset V) →
      U.card ≤ 3 →
      ¬ BlockDeficient
        (fun v => 2 ^ exponent v)
        (enlargedProjectedCandidateBlock C exponent)
        U := by
  classical
  intro U hsub hcardU
  by_cases hU0 : U.card = 0
  · have hU : U = ∅ := Finset.card_eq_zero.mp hU0
    subst U
    simp [BlockDeficient]
  by_cases hU1 : U.card = 1
  · obtain ⟨v,rfl⟩ := Finset.card_eq_one.mp hU1
    have hv : v = s ∨ v = x ∨ v = y ∨ v = z := by
      have := hsub (by simp : v ∈ ({v} : Finset V))
      simpa using this
    rcases hv with rfl | rfl | rfl | rfl
    · unfold BlockDeficient
      simp [hsSecond]
      have hcap :
          2 ≤ (enlargedProjectedCandidateBlock C exponent s).card :=
        enlargedProjectedCandidateBlock_local_capacity
          C exponent
          (by intro q; omega)
          (by intro q; omega)
          (by
            intro q
            by_cases hqLoss : q ∈ projectedLossVertices C exponent
            · have hq := (mem_projectedLossVertices C exponent q).1 hqLoss
              unfold projectedFree at hq
              omega
            · have hq := (mem_projectedLossVertices C exponent q).not.mp hqLoss
              unfold projectedFree at hq
              omega)
          s
      omega
    · unfold BlockDeficient
      simp [hxSecond]
      have hcap :
          2 ≤ (enlargedProjectedCandidateBlock C exponent x).card :=
        enlargedProjectedCandidateBlock_local_capacity
          C exponent
          (by intro q; omega)
          (by intro q; omega)
          (by
            intro q
            by_cases hqLoss : q ∈ projectedLossVertices C exponent
            · have hq := (mem_projectedLossVertices C exponent q).1 hqLoss
              unfold projectedFree at hq
              omega
            · have hq := (mem_projectedLossVertices C exponent q).not.mp hqLoss
              unfold projectedFree at hq
              omega)
          x
      omega
    · unfold BlockDeficient
      simp [hySecond]
      have hcap :
          2 ≤ (enlargedProjectedCandidateBlock C exponent y).card :=
        enlargedProjectedCandidateBlock_local_capacity
          C exponent
          (by intro q; omega)
          (by intro q; omega)
          (by
            intro q
            by_cases hqLoss : q ∈ projectedLossVertices C exponent
            · have hq := (mem_projectedLossVertices C exponent q).1 hqLoss
              unfold projectedFree at hq
              omega
            · have hq := (mem_projectedLossVertices C exponent q).not.mp hqLoss
              unfold projectedFree at hq
              omega)
          y
      omega
    · unfold BlockDeficient
      simp [hzSecond]
      have hcap :
          2 ≤ (enlargedProjectedCandidateBlock C exponent z).card :=
        enlargedProjectedCandidateBlock_local_capacity
          C exponent
          (by intro q; omega)
          (by intro q; omega)
          (by
            intro q
            by_cases hqLoss : q ∈ projectedLossVertices C exponent
            · have hq := (mem_projectedLossVertices C exponent q).1 hqLoss
              unfold projectedFree at hq
              omega
            · have hq := (mem_projectedLossVertices C exponent q).not.mp hqLoss
              unfold projectedFree at hq
              omega)
          z
      omega
  -- For two or three vertices, it suffices that their block union contains
  -- the common Q/T/T/T word plus enough singleton completion bases.  We use
  -- the exact four-block geometry and brute-force the finite subset of four
  -- vertices.
  have hcard23 : U.card = 2 ∨ U.card = 3 := by omega
  -- Rewrite U by extensional membership into one of the eleven nontrivial
  -- subsets of the four named vertices; simp then reduces the Hall inequality
  -- to the already established radius-one block memberships.
  rcases hcard23 with h2 | h3
  · have hsum : (∑ v ∈ U, 2 ^ exponent v) = 4 := by
      have hall : ∀ v ∈ U, exponent v = 1 := by
        intro v hv
        have hv4 := hsub hv
        simp only [Finset.mem_insert, Finset.mem_singleton] at hv4
        rcases hv4 with rfl | rfl | rfl | rfl
        · exact hsSecond
        · exact hxSecond
        · exact hySecond
        · exact hzSecond
      calc
        (∑ v ∈ U, 2 ^ exponent v)
            = ∑ _v ∈ U, 2 := by
                apply Finset.sum_congr rfl
                intro v hv
                rw [hall v hv]
                norm_num
        _ = 2 * U.card := by simp
        _ = 4 := by rw [h2]
    unfold BlockDeficient
    rw [hsum]
    have hpairLower :
        4 ≤ (U.biUnion
          (enlargedProjectedCandidateBlock C exponent)).card := by
      -- each second-layer block has four words, and U is nonempty
      obtain ⟨v,hvU⟩ := Finset.card_pos.mp (by omega : 0 < U.card)
      have hv4 := hsub hvU
      have hvCard :
          (enlargedProjectedCandidateBlock C exponent v).card = 4 := by
        simp only [Finset.mem_insert, Finset.mem_singleton] at hv4
        rcases hv4 with rfl | rfl | rfl | rfl
        · rw [enlargedProjectedCandidateBlock_loss C exponent hsLoss]
          rw [allActiveLossCandidateBlock_card]
          rw [secondLayer_fin3_retainedActive_eq_univ
            C exponent hsLoss hsSecond]
          rw [retainedCompletionWords_card]
          simp [hsSecond]
        · rw [enlargedProjectedCandidateBlock_loss C exponent hxLoss]
          rw [allActiveLossCandidateBlock_card]
          rw [secondLayer_fin3_retainedActive_eq_univ
            C exponent hxLoss hxSecond]
          rw [retainedCompletionWords_card]
          simp [hxSecond]
        · rw [enlargedProjectedCandidateBlock_loss C exponent hyLoss]
          rw [allActiveLossCandidateBlock_card]
          rw [secondLayer_fin3_retainedActive_eq_univ
            C exponent hyLoss hySecond]
          rw [retainedCompletionWords_card]
          simp [hySecond]
        · rw [enlargedProjectedCandidateBlock_loss C exponent hzLoss]
          rw [allActiveLossCandidateBlock_card]
          rw [secondLayer_fin3_retainedActive_eq_univ
            C exponent hzLoss hzSecond]
          rw [retainedCompletionWords_card]
          simp [hzSecond]
      have hsubBlock :
          enlargedProjectedCandidateBlock C exponent v ⊆
            U.biUnion (enlargedProjectedCandidateBlock C exponent) := by
        intro q hq
        exact Finset.mem_biUnion.mpr ⟨v,hvU,hq⟩
      have hc := Finset.card_le_card hsubBlock
      rw [hvCard] at hc
      exact hc
    omega
  · have hsum : (∑ v ∈ U, 2 ^ exponent v) = 6 := by
      have hall : ∀ v ∈ U, exponent v = 1 := by
        intro v hv
        have hv4 := hsub hv
        simp only [Finset.mem_insert, Finset.mem_singleton] at hv4
        rcases hv4 with rfl | rfl | rfl | rfl
        · exact hsSecond
        · exact hxSecond
        · exact hySecond
        · exact hzSecond
      calc
        (∑ v ∈ U, 2 ^ exponent v)
            = ∑ _v ∈ U, 2 := by
                apply Finset.sum_congr rfl
                intro v hv
                rw [hall v hv]
                norm_num
        _ = 2 * U.card := by simp
        _ = 6 := by rw [h3]
    unfold BlockDeficient
    rw [hsum]
    -- Any three of the four radius-one balls contain at least six words.
    -- A direct inclusion-exclusion-free lower bound comes from one complete
    -- four-word block plus the two distinct completion bases of the other two.
    obtain ⟨a,haU,b,hbU,c,hcU,hab,hac,hbc,hUeq⟩ :=
      Finset.card_eq_three.mp h3
    subst U
    -- Every such triple is one of four named triples.
    have ha4 := hsub (by simp : a ∈ ({a,b,c} : Finset V))
    have hb4 := hsub (by simp : b ∈ ({a,b,c} : Finset V))
    have hc4 := hsub (by simp : c ∈ ({a,b,c} : Finset V))
    -- finite four-vertex exhaustion
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha4 hb4 hc4
    rcases ha4 with rfl | rfl | rfl | rfl <;>
      rcases hb4 with rfl | rfl | rfl | rfl <;>
      rcases hc4 with rfl | rfl | rfl | rfl <;>
      try contradiction <;>
      simp [BlockDeficient,hsSecond,hxSecond,hySecond,hzSecond] <;>
      omega

/-- The four Q/T/T/T vertices form an inclusion-minimal deficient family. -/
theorem QTTT_fin3_four_vertices_minimal_deficient
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
      ({s,x,y,z} : Finset V)
    ∧
    ∀ U : Finset V,
      U ⊂ ({s,x,y,z} : Finset V) →
      ¬ BlockDeficient
        (fun v => 2 ^ exponent v)
        (enlargedProjectedCandidateBlock C exponent)
        U := by
  constructor
  · exact QTTT_fin3_four_vertices_blockDeficient
      C exponent
      hsx hsy hsz hxy hxz hyz
      hsLoss hxLoss hyLoss hzLoss
      hsSecond hxSecond hySecond hzSecond
      hcxy hcxz hcyz hsQ hxT hyT hzT
  · intro U hproper
    have hcardU :
        U.card ≤ 3 := by
      have hlt := Finset.card_lt_card hproper
      have hfour :
          ({s,x,y,z} : Finset V).card = 4 := by
        simp [hsx,hsy,hsz,hxy,hxz,hyz,
          Ne.symm hsx,Ne.symm hsy,Ne.symm hsz,
          Ne.symm hxy,Ne.symm hxz,Ne.symm hyz]
      rw [hfour] at hlt
      omega
    exact QTTT_fin3_three_vertex_subsets_not_deficient
      C exponent
      hsx hsy hsz hxy hxz hyz
      hsLoss hxLoss hyLoss hzLoss
      hsSecond hxSecond hySecond hzSecond
      hcxy hcxz hcyz hsQ hxT hyT hzT
      U hproper.1 hcardU

#print axioms QTTT_fin3_three_vertex_subsets_not_deficient
#print axioms QTTT_fin3_four_vertices_minimal_deficient

end OrderedEdgeColoring
end JSP000404Research
