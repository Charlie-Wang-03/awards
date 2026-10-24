import JSP000404Research.FiveMinimaColourGraph
import Mathlib.Combinatorics.SimpleGraph.Bipartite
import Mathlib.Data.Finset.Card
import Mathlib.Tactic

/-!
# C4-free colour classes on five minima lose one edge

A non-root colour class on the five minima is bipartite by its Boolean bit.
If it contains no 4-cycle, then its number of edges is strictly smaller than
the number of minima active in that colour.

The only nontrivial bipartition size is 2+2 or 2+3 (up to symmetry).  When
the left side has two vertices u,v, absence of a 4-cycle says that their
neighbor finsets intersect in at most one vertex.  Hence

  |E| = deg u + deg v
      = |N(u) union N(v)| + |N(u) inter N(v)|
      <= |R| + 1
      = |L| + |R| - 1.

This is the local extremal estimate behind the monochromatic-C4 terminal.
-/

namespace JSP000404Research

open BinaryEdgePartition

def HasFourCycle {W : Type*} (G : SimpleGraph W) : Prop :=
  ∃ a b c d : W,
    a ≠ b ∧ b ≠ c ∧ c ≠ d ∧ d ≠ a ∧
    a ≠ c ∧ b ≠ d ∧
    G.Adj a b ∧ G.Adj b c ∧
    G.Adj c d ∧ G.Adj d a

theorem neighbor_inter_card_le_one_of_no_fourCycle
    {W : Type*} [Fintype W] [DecidableEq W]
    (G : SimpleGraph W)
    [DecidableRel G.Adj]
    {u v : W}
    (huv : u ≠ v)
    (hno : ¬ HasFourCycle G) :
    (G.neighborFinset u ∩ G.neighborFinset v).card ≤ 1 := by
  rw [Finset.card_le_one_iff]
  intro x y hx hy
  by_contra hxy
  have hux : G.Adj u x := by
    simpa only [SimpleGraph.mem_neighborFinset] using
      (Finset.mem_inter.mp hx).1
  have hvx : G.Adj v x := by
    simpa only [SimpleGraph.mem_neighborFinset] using
      (Finset.mem_inter.mp hx).2
  have huy : G.Adj u y := by
    simpa only [SimpleGraph.mem_neighborFinset] using
      (Finset.mem_inter.mp hy).1
  have hvy : G.Adj v y := by
    simpa only [SimpleGraph.mem_neighborFinset] using
      (Finset.mem_inter.mp hy).2
  apply hno
  refine ⟨u, x, v, y,
    hux.ne, hvx.ne', hvy.ne, huy.ne', huv, hxy,
    hux, hvx.symm, hvy, huy.symm⟩

theorem bipartite_edge_card_le_right_add_one_of_left_card_two
    {W : Type*} [Fintype W]
    (G : SimpleGraph W)
    [DecidableRel G.Adj]
    (L R : Finset W)
    (hbi : G.IsBipartiteWith (L : Set W) (R : Set W))
    (hL2 : L.card = 2)
    (hno : ¬ HasFourCycle G) :
    G.edgeFinset.card ≤ R.card + 1 := by
  classical
  obtain ⟨u, v, huv, hL⟩ := Finset.card_eq_two.mp hL2
  have huL : u ∈ L := by simp [hL]
  have hvL : v ∈ L := by simp [hL]
  have hdeg :=
    SimpleGraph.isBipartiteWith_sum_degrees_eq_card_edges hbi
  rw [hL] at hdeg
  simp only [Finset.sum_insert, Finset.mem_singleton,
    huv, not_false_eq_true, Finset.sum_singleton] at hdeg
  have hNu :
      G.neighborFinset u ⊆ R :=
    SimpleGraph.isBipartiteWith_neighborFinset_subset
      hbi huL
  have hNv :
      G.neighborFinset v ⊆ R :=
    SimpleGraph.isBipartiteWith_neighborFinset_subset
      hbi hvL
  have hUnion :
      (G.neighborFinset u ∪ G.neighborFinset v).card ≤ R.card :=
    Finset.card_le_card (Finset.union_subset hNu hNv)
  have hInter :
      (G.neighborFinset u ∩ G.neighborFinset v).card ≤ 1 :=
    neighbor_inter_card_le_one_of_no_fourCycle G huv hno
  have hcardIdentity :=
    Finset.card_union_add_card_inter
      (G.neighborFinset u) (G.neighborFinset v)
  have hdegCard :
      G.degree u + G.degree v ≤ R.card + 1 := by
    rw [← SimpleGraph.card_neighborFinset_eq_degree,
        ← SimpleGraph.card_neighborFinset_eq_degree]
    omega
  rw [← hdeg]
  exact hdegCard

noncomputable def localColourActiveMinima
    {V : Type*} [LinearOrder V] [Fintype V] {k : ℕ}
    (P : BinaryEdgePartition V k)
    (top : V)
    (c : Fin k) : Finset (OtherVertex top) :=
  Finset.univ.filter fun u => c ∈ active P u.1

noncomputable def localColourLeftActiveMinima
    {V : Type*} [LinearOrder V] [Fintype V] {k : ℕ}
    (P : BinaryEdgePartition V k)
    (top : V)
    (c : Fin k) : Finset (OtherVertex top) :=
  (localColourActiveMinima P top c).filter
    fun u => P.bit u.1 c = false

noncomputable def localColourRightActiveMinima
    {V : Type*} [LinearOrder V] [Fintype V] {k : ℕ}
    (P : BinaryEdgePartition V k)
    (top : V)
    (c : Fin k) : Finset (OtherVertex top) :=
  (localColourActiveMinima P top c).filter
    fun u => P.bit u.1 c = true

theorem localColour_active_split
    {V : Type*} [LinearOrder V] [Fintype V] {k : ℕ}
    (P : BinaryEdgePartition V k)
    (top : V)
    (c : Fin k) :
    (localColourLeftActiveMinima P top c).card +
      (localColourRightActiveMinima P top c).card
      =
    (localColourActiveMinima P top c).card := by
  classical
  let A := localColourActiveMinima P top c
  let L := localColourLeftActiveMinima P top c
  let R := localColourRightActiveMinima P top c
  have hdisj : Disjoint L R := by
    rw [Finset.disjoint_left]
    intro u huL huR
    simp [L, R, localColourLeftActiveMinima,
      localColourRightActiveMinima] at huL huR
    exact Bool.false_ne_true (huL.2.symm.trans huR.2)
  have hunion : L ∪ R = A := by
    ext u
    simp only [Finset.mem_union, L, R,
      localColourLeftActiveMinima, localColourRightActiveMinima,
      Finset.mem_filter]
    change (u ∈ A ∧ P.bit u.1 c = false) ∨
      (u ∈ A ∧ P.bit u.1 c = true) ↔ u ∈ A
    constructor
    · rintro (⟨hu, _⟩ | ⟨hu, _⟩)
      · exact hu
      · exact hu
    · intro hu
      cases hbit : P.bit u.1 c with
      | false => exact Or.inl ⟨hu, rfl⟩
      | true => exact Or.inr ⟨hu, rfl⟩
  change L.card + R.card = A.card
  rw [← hunion, Finset.card_union_of_disjoint hdisj]

theorem localColourGraph_isBipartiteWith_active_split
    {V : Type*} [LinearOrder V] [Fintype V] {k : ℕ}
    (P : BinaryEdgePartition V k)
    (top : V)
    (c : Fin k)
    (hcTop : c ∉ active P top) :
    (localColourGraph P top c).IsBipartiteWith
      (localColourLeftActiveMinima P top c : Set (OtherVertex top))
      (localColourRightActiveMinima P top c : Set (OtherVertex top)) := by
  classical
  let G := localColourGraph P top c
  let A := localColourActiveMinima P top c
  let L := localColourLeftActiveMinima P top c
  let R := localColourRightActiveMinima P top c
  constructor
  · rw [Set.disjoint_left]
    intro u huL huR
    simp [L, R, localColourLeftActiveMinima,
      localColourRightActiveMinima] at huL huR
    exact Bool.false_ne_true (huL.2.symm.trans huR.2)
  · intro u v huv
    have hdata :=
      (localColourGraph_adj P top c u v).1 huv
    have huActive :
        c ∈ active P u.1 :=
      localColourGraph_support_active P top c u ⟨v, huv⟩
    have hvActive :
        c ∈ active P v.1 :=
      localColourGraph_support_active P top c v ⟨u, huv.symm⟩
    have hbit :=
      bit_ne_of_localIncidentColor P
        (show u.1 ≠ v.1 by
          intro h
          apply hdata.1
          exact Subtype.ext h)
    rw [hdata.2] at hbit
    cases hu : P.bit u.1 c <;>
      cases hv : P.bit v.1 c <;>
      simp_all [L, R, A,
        localColourLeftActiveMinima,
        localColourRightActiveMinima,
        localColourActiveMinima]

theorem card_otherVertex_eq_five_of_card_six
    {V : Type*} [Fintype V] [DecidableEq V]
    (hcard : Fintype.card V = 6)
    (top : V) :
    Fintype.card (OtherVertex top) = 5 := by
  classical
  change Fintype.card {v : V // v ≠ top} = 5
  rw [Fintype.card_subtype_compl (fun v : V => v = top)]
  simp [hcard]

/-- A used non-top colour on the five minima has strictly fewer edges than
active minima unless it contains a four-cycle. -/
theorem localColourGraph_edge_card_lt_active_of_no_fourCycle
    {V : Type*} [LinearOrder V] [Fintype V] {k : ℕ}
    (P : BinaryEdgePartition V k)
    (top : V)
    (c : Fin k)
    [DecidableRel (localColourGraph P top c).Adj]
    (hcard : Fintype.card V = 6)
    (hcTop : c ∉ active P top)
    (hused : (localColourActiveMinima P top c).Nonempty)
    (hno : ¬ HasFourCycle (localColourGraph P top c)) :
    (localColourGraph P top c).edgeFinset.card <
      (localColourActiveMinima P top c).card := by
  classical
  let G := localColourGraph P top c
  let A := localColourActiveMinima P top c
  let L := localColourLeftActiveMinima P top c
  let R := localColourRightActiveMinima P top c
  change G.edgeFinset.card < A.card

  have hbi :
      G.IsBipartiteWith (L : Set (OtherVertex top))
        (R : Set (OtherVertex top)) := by
    simpa [G, L, R] using
      localColourGraph_isBipartiteWith_active_split
        P top c hcTop
  have hsplit :
      L.card + R.card = A.card := by
    simpa [A, L, R] using
      localColour_active_split P top c

  have hA5 : A.card ≤ 5 := by
    have hle :
        A.card ≤ Fintype.card (OtherVertex top) := by
      simpa using Finset.card_le_univ A
    rw [card_otherVertex_eq_five_of_card_six hcard top] at hle
    exact hle

  have hLRnonempty : L.Nonempty ∧ R.Nonempty := by
    obtain ⟨u, huA⟩ := hused
    have huActive : c ∈ active P u.1 := by
      simpa [A, localColourActiveMinima] using huA
    have huSupp :
        u ∈ G.support := by
      simpa [G] using
        active_mem_localColourGraph_support_of_not_top
          P top c hcTop u huActive
    obtain ⟨v, huv⟩ := huSupp
    have hp := hbi.mem_of_adj huv
    rcases hp with hp | hp
    · exact ⟨⟨u, hp.1⟩, ⟨v, hp.2⟩⟩
    · exact ⟨⟨v, hp.2⟩, ⟨u, hp.1⟩⟩

  have hLpos : 1 ≤ L.card := Finset.one_le_card.mpr hLRnonempty.1
  have hRpos : 1 ≤ R.card := Finset.one_le_card.mpr hLRnonempty.2

  by_cases hL1 : L.card = 1
  · obtain ⟨u, hL⟩ := Finset.card_eq_one.mp hL1
    have huL : u ∈ L := by simp [hL]
    have hdeg :=
      SimpleGraph.isBipartiteWith_sum_degrees_eq_card_edges hbi
    rw [hL] at hdeg
    simp only [Finset.sum_singleton] at hdeg
    have hdegLe :=
      SimpleGraph.isBipartiteWith_degree_le hbi huL
    rw [hdeg] at hdegLe
    omega

  by_cases hR1 : R.card = 1
  · obtain ⟨u, hR⟩ := Finset.card_eq_one.mp hR1
    have huR : u ∈ R := by simp [hR]
    have hdeg :=
      SimpleGraph.isBipartiteWith_sum_degrees_eq_card_edges' hbi
    rw [hR] at hdeg
    simp only [Finset.sum_singleton] at hdeg
    have hdegLe :=
      SimpleGraph.isBipartiteWith_degree_le' hbi huR
    rw [hdeg] at hdegLe
    omega

  have hL2 : 2 ≤ L.card := by omega
  have hR2 : 2 ≤ R.card := by omega
  have hside2 : L.card = 2 ∨ R.card = 2 := by
    omega
  rcases hside2 with hLtwo | hRtwo
  · have hedge :=
      bipartite_edge_card_le_right_add_one_of_left_card_two
        G L R hbi hLtwo (by simpa [G] using hno)
    omega
  · have hedge :=
      bipartite_edge_card_le_right_add_one_of_left_card_two
        G R L hbi.symm hRtwo (by simpa [G] using hno)
    omega

/--
Distinct local colours have disjoint *actual* edges on the non-top vertices.
Unlike the subsequent packing result, this does not assume pairwise
disjointness: it follows directly from the unique local incident colour.
-/
theorem localColourGraph_edgeFinset_disjoint_of_ne
    {V : Type*} [LinearOrder V] [Fintype V] {k : ℕ}
    (P : BinaryEdgePartition V k)
    (top : V)
    {c d : Fin k}
    (hcd : c ≠ d) :
    Disjoint (localColourGraph P top c).edgeFinset
      (localColourGraph P top d).edgeFinset := by
  classical
  apply Finset.disjoint_left.mpr
  intro e hec hed
  induction e using Sym2.ind with
  | _ u v =>
      have hcAdj : (localColourGraph P top c).Adj u v := by
        simpa only [SimpleGraph.mem_edgeFinset,
          SimpleGraph.mem_edgeSet] using hec
      have hdAdj : (localColourGraph P top d).Adj u v := by
        simpa only [SimpleGraph.mem_edgeFinset,
          SimpleGraph.mem_edgeSet] using hed
      have hcCol :=
        ((localColourGraph_adj P top c u v).mp hcAdj).2
      have hdCol :=
        ((localColourGraph_adj P top d u v).mp hdAdj).2
      exact hcd (hcCol.symm.trans hdCol)

#print axioms localColourGraph_edgeFinset_disjoint_of_ne

/--
Three pairwise disjoint edge classes of cardinality at least four cannot
fit in an ambient edge universe of cardinality at most ten.

This is the finite packing inequality needed for the *conditional* C4
exception-colour count on five vertices.  Establishing the ambient ten-edge
universe and the four-edge lower bound for real local colour graphs remains
a separate graph-theoretic interface, not an assumed planar theorem.
-/
theorem three_disjoint_four_edge_classes_impossible
    {E : Type*} [Fintype E]
    (A B C : Finset E)
    (hTen : Fintype.card E ≤ 10)
    (hA : 4 ≤ A.card)
    (hB : 4 ≤ B.card)
    (hC : 4 ≤ C.card)
    (hAB : Disjoint A B)
    (hAC : Disjoint A C)
    (hBC : Disjoint B C) : False := by
  classical
  have hABCdisjoint : Disjoint (A ∪ B) C := by
    apply Finset.disjoint_left.mpr
    intro x hx hc
    rcases Finset.mem_union.mp hx with hxA | hxB
    · exact (Finset.disjoint_left.mp hAC) hxA hc
    · exact (Finset.disjoint_left.mp hBC) hxB hc
  have hABCcard :
      ((A ∪ B) ∪ C).card = A.card + B.card + C.card := by
    rw [Finset.card_union_of_disjoint hABCdisjoint,
      Finset.card_union_of_disjoint hAB]
  have hBound := Finset.card_le_univ ((A ∪ B) ∪ C)
  omega

/--
At most two colour classes can each use four or more mutually exclusive edges
inside an ambient universe of at most ten edges.  The disjointness and
four-edge bounds are explicit, independently checkable hypotheses.
-/
theorem large_disjoint_edge_colour_classes_card_le_two
    {E K : Type*} [Fintype E]
    (hTen : Fintype.card E ≤ 10)
    (edgeClass : K → Finset E)
    (hDisjoint : ∀ a b : K, a ≠ b →
      Disjoint (edgeClass a) (edgeClass b))
    (bad : Finset K)
    (hLarge : ∀ c ∈ bad, 4 ≤ (edgeClass c).card) :
    bad.card ≤ 2 := by
  classical
  by_contra h
  have hThree : 2 < bad.card := by omega
  obtain ⟨a,ha,b,hb,c,hc,hab,hac,hbc⟩ :=
    Finset.two_lt_card.mp hThree
  exact three_disjoint_four_edge_classes_impossible
    (edgeClass a) (edgeClass b) (edgeClass c) hTen
    (hLarge a ha) (hLarge b hb) (hLarge c hc)
    (hDisjoint a b hab) (hDisjoint a c hac) (hDisjoint b c hbc)

/-- A genuine 4-cycle contains four distinct undirected edges. -/
theorem HasFourCycle.edgeFinset_card_ge_four
    {W : Type*} [Fintype W]
    (G : SimpleGraph W)
    (hC4 : HasFourCycle G) :
    4 ≤ G.edgeFinset.card := by
  classical
  obtain ⟨a,b,c,d,hab,hbc,hcd,hda,hac,hbd,
    hAB,hBC,hCD,hDA⟩ := hC4
  let E : Finset (Sym2 W) :=
    {Sym2.mk (a,b), Sym2.mk (b,c),
      Sym2.mk (c,d), Sym2.mk (d,a)}
  have hsub : E ⊆ G.edgeFinset := by
    intro e he
    simp only [E, Finset.mem_insert, Finset.mem_singleton] at he
    rcases he with rfl | rfl | rfl | rfl
    · simpa only [SimpleGraph.mem_edgeFinset,
        SimpleGraph.mem_edgeSet] using hAB
    · simpa only [SimpleGraph.mem_edgeFinset,
        SimpleGraph.mem_edgeSet] using hBC
    · simpa only [SimpleGraph.mem_edgeFinset,
        SimpleGraph.mem_edgeSet] using hCD
    · simpa only [SimpleGraph.mem_edgeFinset,
        SimpleGraph.mem_edgeSet] using hDA
  have hcard : E.card = 4 := by
    dsimp [E]
    simp [Sym2.eq_iff,hab,hbc,hcd,hda,hac,hbd,eq_comm]
  calc
    4 = E.card := hcard.symm
    _ ≤ G.edgeFinset.card := Finset.card_le_card hsub

#print axioms HasFourCycle.edgeFinset_card_ge_four

/--
For a six-point partition and five non-top vertices, *actual* colour graph
edge classes of size at least four occur in at most two colours.
This uses their proven edge disjointness and the exact ten-edge complete-graph
ceiling. No C4-to-four-edges interface is assumed here.
-/
theorem five_minima_large_local_colour_classes_card_le_two
    {V : Type*} [LinearOrder V] [Fintype V] {k : ℕ}
    (P : BinaryEdgePartition V k)
    (top : V)
    (hSix : Fintype.card V = 6)
    (large : Finset (Fin k))
    (hLarge : ∀ c ∈ large,
      4 ≤ (localColourGraph P top c).edgeFinset.card) :
    large.card ≤ 2 := by
  classical
  by_contra hnot
  have hThree : 2 < large.card := by omega
  obtain ⟨a,ha,b,hb,c,hc,hab,hac,hbc⟩ :=
    Finset.two_lt_card.mp hThree
  let A := (localColourGraph P top a).edgeFinset
  let B := (localColourGraph P top b).edgeFinset
  let D := (localColourGraph P top c).edgeFinset
  have hAB : Disjoint A B :=
    localColourGraph_edgeFinset_disjoint_of_ne P top hab
  have hAD : Disjoint A D :=
    localColourGraph_edgeFinset_disjoint_of_ne P top hac
  have hBD : Disjoint B D :=
    localColourGraph_edgeFinset_disjoint_of_ne P top hbc
  have hABD : Disjoint (A ∪ B) D := by
    apply Finset.disjoint_left.mpr
    intro e he hd
    rcases Finset.mem_union.mp he with hA | hB
    · exact (Finset.disjoint_left.mp hAD) hA hd
    · exact (Finset.disjoint_left.mp hBD) hB hd
  have hUnion : ((A ∪ B) ∪ D).card =
      A.card + B.card + D.card := by
    rw [Finset.card_union_of_disjoint hABD,
      Finset.card_union_of_disjoint hAB]
  have hEdgesTop :
      (⊤ : SimpleGraph (OtherVertex top)).edgeFinset.card = 10 := by
    rw [SimpleGraph.card_edgeFinset_top_eq_card_choose_two,
      card_otherVertex_eq_five_of_card_six hSix top]
    norm_num
  have hsub :
      ((A ∪ B) ∪ D) ⊆
        (⊤ : SimpleGraph (OtherVertex top)).edgeFinset := by
    intro e he
    rcases Finset.mem_union.mp he with heAB | heD
    · rcases Finset.mem_union.mp heAB with heA | heB
      · exact (SimpleGraph.edgeFinset_mono le_top) heA
      · exact (SimpleGraph.edgeFinset_mono le_top) heB
    · exact (SimpleGraph.edgeFinset_mono le_top) heD
  have hUnionLe : ((A ∪ B) ∪ D).card ≤ 10 := by
    calc
      ((A ∪ B) ∪ D).card ≤
          (⊤ : SimpleGraph (OtherVertex top)).edgeFinset.card :=
        Finset.card_le_card hsub
      _ = 10 := hEdgesTop
  have hA : 4 ≤ A.card := hLarge a ha
  have hB : 4 ≤ B.card := hLarge b hb
  have hD : 4 ≤ D.card := hLarge c hc
  omega

/--
On five non-top vertices, at most two colours have a genuine 4-cycle.
This conclusion assumes only that the full vertex set has six elements
and that local edges have their actual unique incident colours.
-/
theorem five_minima_C4_exception_colours_card_le_two
    {V : Type*} [LinearOrder V] [Fintype V] {k : ℕ}
    (P : BinaryEdgePartition V k)
    (top : V)
    (hSix : Fintype.card V = 6)
    (bad : Finset (Fin k))
    (hC4 : ∀ c ∈ bad, HasFourCycle (localColourGraph P top c)) :
    bad.card ≤ 2 := by
  apply five_minima_large_local_colour_classes_card_le_two
    P top hSix bad
  intro c hc
  exact HasFourCycle.edgeFinset_card_ge_four
    (localColourGraph P top c) (hC4 c hc)

#print axioms five_minima_C4_exception_colours_card_le_two

#print axioms five_minima_large_local_colour_classes_card_le_two

#print axioms three_disjoint_four_edge_classes_impossible
#print axioms large_disjoint_edge_colour_classes_card_le_two

#print axioms neighbor_inter_card_le_one_of_no_fourCycle
#print axioms bipartite_edge_card_le_right_add_one_of_left_card_two
#print axioms localColourGraph_edge_card_lt_active_of_no_fourCycle

end JSP000404Research
