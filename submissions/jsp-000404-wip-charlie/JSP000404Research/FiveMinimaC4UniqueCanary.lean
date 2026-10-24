import JSP000404Research.FiveMinimaC4Extremal
import Mathlib.Tactic

/-!
# Five-vertex 4-cycles: strict uniqueness of an exceptional colour

This isolated branch checks a stronger five-minima obstruction: two 4-cycles in
the complete graph on five vertices necessarily share an unordered edge.
It is proved by a finite, kernel-evaluated five-vertex verification and
transported to an arbitrary vertex type of cardinality five.

No additional axiom, sorry, or angle hypothesis is introduced.  This
isolated research module is not imported by the global JSP-000404 theorem.
-/

namespace JSP000404Research

private def cycleEdgeSet {W : Type*} [DecidableEq W]
    (a b c d : W) : Finset (Sym2 W) :=
  {Sym2.mk (a,b), Sym2.mk (b,c),
    Sym2.mk (c,d), Sym2.mk (d,a)}

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem finFive_distinct_fourCycles_share_edge :
    ∀ a b c d e f g h : Fin 5,
      a ≠ b → b ≠ c → c ≠ d → d ≠ a →
      a ≠ c → b ≠ d →
      e ≠ f → f ≠ g → g ≠ h → h ≠ e →
      e ≠ g → f ≠ h →
      (cycleEdgeSet a b c d ∩
        cycleEdgeSet e f g h).Nonempty := by
  decide

private theorem distinct_fourCycles_share_edge_of_card_five
    {W : Type*} [Fintype W]
    (hFive : Fintype.card W = 5)
    {a b c d e f g h : W}
    (hab : a ≠ b) (hbc : b ≠ c)
    (hcd : c ≠ d) (hda : d ≠ a)
    (hac : a ≠ c) (hbd : b ≠ d)
    (hef : e ≠ f) (hfg : f ≠ g)
    (hgh : g ≠ h) (hhe : h ≠ e)
    (heg : e ≠ g) (hfh : f ≠ h) :
    (cycleEdgeSet a b c d ∩
      cycleEdgeSet e f g h).Nonempty := by
  classical
  let φ : W ≃ Fin 5 := Fintype.equivFinOfCardEq hFive
  let E : Sym2 W ↪ Sym2 (Fin 5) :=
    ⟨Sym2.map φ, Sym2.map.injective φ.injective⟩
  have hFin :
      (cycleEdgeSet (φ a) (φ b) (φ c) (φ d) ∩
        cycleEdgeSet (φ e) (φ f) (φ g) (φ h)).Nonempty := by
    apply finFive_distinct_fourCycles_share_edge
    all_goals
      intro heq
      first
      | exact hab (φ.injective heq)
      | exact hbc (φ.injective heq)
      | exact hcd (φ.injective heq)
      | exact hda (φ.injective heq)
      | exact hac (φ.injective heq)
      | exact hbd (φ.injective heq)
      | exact hef (φ.injective heq)
      | exact hfg (φ.injective heq)
      | exact hgh (φ.injective heq)
      | exact hhe (φ.injective heq)
      | exact heg (φ.injective heq)
      | exact hfh (φ.injective heq)
  have hMapA :
      (cycleEdgeSet a b c d).map E =
        cycleEdgeSet (φ a) (φ b) (φ c) (φ d) := by
    simp [cycleEdgeSet, E, Sym2.map_mk]
  have hMapB :
      (cycleEdgeSet e f g h).map E =
        cycleEdgeSet (φ e) (φ f) (φ g) (φ h) := by
    simp [cycleEdgeSet, E, Sym2.map_mk]
  have hMap :
      (cycleEdgeSet a b c d ∩ cycleEdgeSet e f g h).map E =
        (cycleEdgeSet (φ a) (φ b) (φ c) (φ d) ∩
          cycleEdgeSet (φ e) (φ f) (φ g) (φ h)) := by
    rw [Finset.map_inter, hMapA, hMapB]
  obtain ⟨z,hz⟩ := hFin
  have hMapped : z ∈
      (cycleEdgeSet a b c d ∩ cycleEdgeSet e f g h).map E := by
    rw [hMap]
    exact hz
  obtain ⟨w,hw,_⟩ := Finset.mem_map.mp hMapped
  exact ⟨w,hw⟩

private theorem cycleEdgeSet_subset_edgeFinset
    {W : Type*} [Fintype W]
    (G : SimpleGraph W)
    {a b c d : W}
    (hab : G.Adj a b)
    (hbc : G.Adj b c)
    (hcd : G.Adj c d)
    (hda : G.Adj d a) :
    cycleEdgeSet a b c d ⊆ G.edgeFinset := by
  classical
  intro edge hmem
  simp only [cycleEdgeSet, Finset.mem_insert,
    Finset.mem_singleton] at hmem
  rcases hmem with rfl | rfl | rfl | rfl
  · simpa only [SimpleGraph.mem_edgeFinset,
      SimpleGraph.mem_edgeSet] using hab
  · simpa only [SimpleGraph.mem_edgeFinset,
      SimpleGraph.mem_edgeSet] using hbc
  · simpa only [SimpleGraph.mem_edgeFinset,
      SimpleGraph.mem_edgeSet] using hcd
  · simpa only [SimpleGraph.mem_edgeFinset,
      SimpleGraph.mem_edgeSet] using hda

/-- Two edge-disjoint simple graphs on five vertices cannot both contain C4. -/
theorem disjoint_graphs_on_five_not_both_C4
    {W : Type*} [Fintype W]
    (hFive : Fintype.card W = 5)
    (G H : SimpleGraph W)
    (hDisjoint : Disjoint G.edgeFinset H.edgeFinset)
    (hG : HasFourCycle G)
    (hH : HasFourCycle H) : False := by
  classical
  obtain ⟨a,b,c,d,hab,hbc,hcd,hda,hac,hbd,
    hAB,hBC,hCD,hDA⟩ := hG
  obtain ⟨e,f,g,h,hef,hfg,hgh,hhe,heg,hfh,
    hEF,hFG,hGH,hHE⟩ := hH
  have hMeet :=
    distinct_fourCycles_share_edge_of_card_five hFive
      hab hbc hcd hda hac hbd hef hfg hgh hhe heg hfh
  obtain ⟨edge,hBoth⟩ := hMeet
  have hInG : edge ∈ G.edgeFinset :=
    cycleEdgeSet_subset_edgeFinset G hAB hBC hCD hDA
      (Finset.mem_inter.mp hBoth).1
  have hInH : edge ∈ H.edgeFinset :=
    cycleEdgeSet_subset_edgeFinset H hEF hFG hGH hHE
      (Finset.mem_inter.mp hBoth).2
  exact (Finset.disjoint_left.mp hDisjoint) hInG hInH

/-- At most one genuine monochromatic 4-cycle colour on five minima. -/
theorem five_minima_C4_exception_colours_card_le_one
    {V : Type*} [LinearOrder V] [Fintype V] {k : ℕ}
    (P : BinaryEdgePartition V k)
    (top : V)
    (hSix : Fintype.card V = 6)
    (bad : Finset (Fin k))
    (hC4 : ∀ c ∈ bad, HasFourCycle (localColourGraph P top c)) :
    bad.card ≤ 1 := by
  classical
  rw [Finset.card_le_one_iff]
  intro c d hc hd
  by_contra hcd
  exact disjoint_graphs_on_five_not_both_C4
    (card_otherVertex_eq_five_of_card_six hSix top)
    (localColourGraph P top c)
    (localColourGraph P top d)
    (localColourGraph_edgeFinset_disjoint_of_ne P top hcd)
    (hC4 c hc) (hC4 d hd)

#print axioms disjoint_graphs_on_five_not_both_C4
#print axioms five_minima_C4_exception_colours_card_le_one

end JSP000404Research
