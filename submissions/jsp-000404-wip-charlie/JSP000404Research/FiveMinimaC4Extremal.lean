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
    {W : Type*} [Fintype W]
    (G : SimpleGraph W)
    [DecidableRel G.Adj]
    {u v : W}
    (huv : u ≠ v)
    (hno : ¬ HasFourCycle G) :
    (G.neighborFinset u ∩ G.neighborFinset v).card ≤ 1 := by
  rw [Finset.card_le_one_iff]
  intro x hx y hy
  by_contra hxy
  have hux : G.Adj u x := by
    exact (SimpleGraph.mem_neighborFinset.mp
      (Finset.mem_inter.mp hx).1)
  have hvx : G.Adj v x := by
    exact (SimpleGraph.mem_neighborFinset.mp
      (Finset.mem_inter.mp hx).2)
  have huy : G.Adj u y := by
    exact (SimpleGraph.mem_neighborFinset.mp
      (Finset.mem_inter.mp hy).1)
  have hvy : G.Adj v y := by
    exact (SimpleGraph.mem_neighborFinset.mp
      (Finset.mem_inter.mp hy).2)
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
  have hunion : L ∪ R = A := by
    ext u
    simp only [Finset.mem_union, Finset.mem_filter]
    constructor
    · rintro (⟨huA, _⟩ | ⟨huA, _⟩)
      · exact huA
      · exact huA
    · intro huA
      cases hbit : P.bit u.1 c <;>
        simp [L, R, localColourLeftActiveMinima,
          localColourRightActiveMinima, huA, hbit]
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
    {V : Type*} [Fintype V]
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

#print axioms neighbor_inter_card_le_one_of_no_fourCycle
#print axioms bipartite_edge_card_le_right_add_one_of_left_card_two
#print axioms localColourGraph_edge_card_lt_active_of_no_fourCycle

end JSP000404Research
