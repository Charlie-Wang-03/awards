import JSP000404Research.SixPointBadActiveC4
import Mathlib.Tactic

/-!
# A bad active vertex is either on a monochromatic C4 or pendant to one

Let G be a bipartite colour-class graph on exactly five minima.  Suppose
a,b,c,d form a four-cycle and a fifth vertex z is active in this colour.

If z has two distinct neighbours on the cycle, bipartiteness forces those
neighbours to be the two vertices in the opposite side of the C4.  One of the
two length-two arcs of the original C4 then combines with z to make another
four-cycle containing z.

Hence, if no four-cycle of this colour contains z, then z has exactly one
neighbour: it is a pendant vertex attached to the existing C4.
-/

namespace JSP000404Research

open BinaryEdgePartition

/-- In a bipartite graph, an off-cycle vertex adjacent to two C4 vertices
belongs to another C4. -/
theorem fourCycle_through_offcycle_vertex_of_two_cycle_neighbors
    {W : Type*}
    (G : SimpleGraph W)
    (hbi : G.IsBipartite)
    {a b c d z x y : W}
    (hab : a ≠ b) (hbc : b ≠ c)
    (hcd : c ≠ d) (hda : d ≠ a)
    (hac : a ≠ c) (hbd : b ≠ d)
    (habE : G.Adj a b)
    (hbcE : G.Adj b c)
    (hcdE : G.Adj c d)
    (hdaE : G.Adj d a)
    (hzA : z ≠ a) (hzB : z ≠ b)
    (hzC : z ≠ c) (hzD : z ≠ d)
    (hxMem : x = a ∨ x = b ∨ x = c ∨ x = d)
    (hyMem : y = a ∨ y = b ∨ y = c ∨ y = d)
    (hxy : x ≠ y)
    (hzx : G.Adj z x)
    (hzy : G.Adj z y) :
    ∃ u v w : W,
      z ≠ u ∧ u ≠ v ∧ v ≠ w ∧ w ≠ z ∧
      z ≠ v ∧ u ≠ w ∧
      G.Adj z u ∧ G.Adj u v ∧
      G.Adj v w ∧ G.Adj w z := by
  rcases hxMem with rfl | rfl | rfl | rfl <;>
    rcases hyMem with rfl | rfl | rfl | rfl
  <;> try { exact False.elim (hxy rfl) }
  all_goals
    first
    | exact ⟨a,b,c,hzA,hab,hbc,hzC,hac,hzx,habE,hbcE,hzy.symm⟩
    | exact ⟨a,d,c,hzA,hda.symm,hcd.symm,hzC,hac,hzx,hdaE.symm,hcdE.symm,hzy.symm⟩
    | exact ⟨b,a,d,hzB,hab.symm,hda,hzD,hbd,hzx,habE.symm,hdaE,hzy.symm⟩
    | exact ⟨b,c,d,hzB,hbc,hcd,hzD,hbd,hzx,hbcE,hcdE,hzy.symm⟩
    | exact ⟨c,b,a,hzC,hbc.symm,hab.symm,hzA,hac,hzx,hbcE.symm,habE.symm,hzy.symm⟩
    | exact ⟨c,d,a,hzC,hcd,hda,hzA,hac,hzx,hcdE,hdaE,hzy.symm⟩
    | exact ⟨d,a,b,hzD,hda.symm,hab,hzB,hbd,hzx,hdaE.symm,habE,hzy.symm⟩
    | exact ⟨d,c,b,hzD,hcd.symm,hbc.symm,hzB,hbd,hzx,hcdE.symm,hbcE.symm,hzy.symm⟩

/-- Five-vertex specialization: if z is active in a C4 colour but no C4 of
that colour contains z, then z has degree exactly one. -/
theorem degree_eq_one_of_active_off_fourCycle_no_cycle_through
    {W : Type*} [Fintype W]
    (G : SimpleGraph W)
    [DecidableRel G.Adj]
    (hcard : Fintype.card W = 5)
    (hbi : G.IsBipartite)
    {a b c d z : W}
    (hab : a ≠ b) (hbc : b ≠ c)
    (hcd : c ≠ d) (hda : d ≠ a)
    (hac : a ≠ c) (hbd : b ≠ d)
    (habE : G.Adj a b)
    (hbcE : G.Adj b c)
    (hcdE : G.Adj c d)
    (hdaE : G.Adj d a)
    (hzA : z ≠ a) (hzB : z ≠ b)
    (hzC : z ≠ c) (hzD : z ≠ d)
    (hzSupport : z ∈ G.support)
    (hnoZ :
      ¬ ∃ u v w : W,
        z ≠ u ∧ u ≠ v ∧ v ≠ w ∧ w ≠ z ∧
        z ≠ v ∧ u ≠ w ∧
        G.Adj z u ∧ G.Adj u v ∧
        G.Adj v w ∧ G.Adj w z) :
    G.degree z = 1 := by
  classical
  have hdegPos : 1 ≤ G.degree z := by
    obtain ⟨u,hzu⟩ := hzSupport
    rw [← SimpleGraph.card_neighborFinset_eq_degree]
    exact Finset.one_le_card.mpr ⟨u, SimpleGraph.mem_neighborFinset.mpr hzu⟩
  have hcycleSet :
      ({a,b,c,d} : Finset W).card = 4 := by
    simp [hab,hbc,hcd,hda,hac,hbd,
      Ne.symm hab,Ne.symm hbc,Ne.symm hcd,
      Ne.symm hda,Ne.symm hac,Ne.symm hbd]
  have hall :
      ∀ x : W, x = z ∨ x = a ∨ x = b ∨ x = c ∨ x = d := by
    intro x
    by_contra hx
    push_neg at hx
    let S : Finset W := {z,a,b,c,d}
    have hfive : S.card = 5 := by
      dsimp [S]
      simp [hx.1, hx.2.1, hx.2.2.1, hx.2.2.2.1,
        hzA,hzB,hzC,hzD,
        hab,hbc,hcd,hda,hac,hbd,
        Ne.symm hzA,Ne.symm hzB,Ne.symm hzC,Ne.symm hzD,
        Ne.symm hab,Ne.symm hbc,Ne.symm hcd,
        Ne.symm hda,Ne.symm hac,Ne.symm hbd]
    have hSuniv : S = Finset.univ := by
      apply Finset.eq_univ_of_card
      rw [hfive, Finset.card_univ, hcard]
    have hxS : x ∈ S := by rw [hSuniv]; simp
    simp [S, hx.1, hx.2.1, hx.2.2.1, hx.2.2.2.1] at hxS

  by_contra hdegNe
  have hdeg2 : 2 ≤ G.degree z := by omega
  rw [← SimpleGraph.card_neighborFinset_eq_degree] at hdeg2
  obtain ⟨x,hxN,y,hyN,hxy⟩ :=
    Finset.two_le_card.mp hdeg2
  have hzx : G.Adj z x :=
    SimpleGraph.mem_neighborFinset.mp hxN
  have hzy : G.Adj z y :=
    SimpleGraph.mem_neighborFinset.mp hyN
  have hxNeZ : x ≠ z := hzx.ne'
  have hyNeZ : y ≠ z := hzy.ne'
  have hxMem :
      x = a ∨ x = b ∨ x = c ∨ x = d := by
    rcases hall x with hxz | hxrest
    · exact False.elim (hxNeZ hxz)
    · exact hxrest
  have hyMem :
      y = a ∨ y = b ∨ y = c ∨ y = d := by
    rcases hall y with hyz | hyrest
    · exact False.elim (hyNeZ hyz)
    · exact hyrest
  apply hnoZ
  exact fourCycle_through_offcycle_vertex_of_two_cycle_neighbors
    G hbi hab hbc hcd hda hac hbd
    habE hbcE hcdE hdaE
    hzA hzB hzC hzD hxMem hyMem hxy hzx hzy

#print axioms degree_eq_one_of_active_off_fourCycle_no_cycle_through

end JSP000404Research
