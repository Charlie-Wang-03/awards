import JSP000404Research.SixPointMergedRepeatedColour
import Mathlib.Combinatorics.SimpleGraph.Bipartite
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Tactic

/-!
# Colour-class graphs on the five non-top vertices

For a BinaryEdgePartition and a distinguished top vertex, each coordinate c
defines an undirected graph on OtherVertex top: two minima are adjacent exactly
when their mutual edge has local incident colour c.

The Boolean coordinate bit(-,c) is an explicit bipartition of this graph.
This packages the exact finite-graph object needed for the remaining
two-exception equality terminal.
-/

namespace JSP000404Research

open BinaryEdgePartition

theorem localIncidentColor_comm
    {V : Type*} [LinearOrder V] {k : ℕ}
    (P : BinaryEdgePartition V k)
    (i j : V) :
    localIncidentColor P i j =
      localIncidentColor P j i := by
  rcases lt_trichotomy i j with hij | hij | hij
  · unfold localIncidentColor
    rw [dif_pos hij, dif_neg (not_lt_of_ge hij.le)]
  · subst j
    rfl
  · unfold localIncidentColor
    rw [dif_neg (not_lt_of_ge hij.le), dif_pos hij]

theorem bit_ne_of_localIncidentColor
    {V : Type*} [LinearOrder V] {k : ℕ}
    (P : BinaryEdgePartition V k)
    {i j : V}
    (hij : i ≠ j) :
    P.bit i (localIncidentColor P i j) ≠
      P.bit j (localIncidentColor P i j) := by
  rcases lt_or_gt_of_ne hij with hij | hji
  · unfold localIncidentColor
    rw [dif_pos hij]
    exact P.proper hij
  · have hnot : ¬ i < j := not_lt_of_ge hji.le
    unfold localIncidentColor
    rw [dif_neg hnot]
    exact (P.proper hji).symm

noncomputable def localColourGraph
    {V : Type*} [LinearOrder V] {k : ℕ}
    (P : BinaryEdgePartition V k)
    (top : V)
    (c : Fin k) :
    SimpleGraph (OtherVertex top) :=
  SimpleGraph.fromRel fun u v =>
    localIncidentColor P u.1 v.1 = c

@[simp] theorem localColourGraph_adj
    {V : Type*} [LinearOrder V] {k : ℕ}
    (P : BinaryEdgePartition V k)
    (top : V)
    (c : Fin k)
    (u v : OtherVertex top) :
    (localColourGraph P top c).Adj u v ↔
      u ≠ v ∧ localIncidentColor P u.1 v.1 = c := by
  rw [localColourGraph, SimpleGraph.fromRel_adj]
  constructor
  · rintro ⟨huv, h | h⟩
    · exact ⟨huv, h⟩
    · exact ⟨huv, by
        rw [localIncidentColor_comm P]
        exact h⟩
  · rintro ⟨huv, h⟩
    exact ⟨huv, Or.inl h⟩

def localColourLeft
    {V : Type*} [LinearOrder V] {k : ℕ}
    (P : BinaryEdgePartition V k)
    (top : V)
    (c : Fin k) : Set (OtherVertex top) :=
  {u | P.bit u.1 c = false}

def localColourRight
    {V : Type*} [LinearOrder V] {k : ℕ}
    (P : BinaryEdgePartition V k)
    (top : V)
    (c : Fin k) : Set (OtherVertex top) :=
  {u | P.bit u.1 c = true}

theorem localColourGraph_isBipartiteWith
    {V : Type*} [LinearOrder V] {k : ℕ}
    (P : BinaryEdgePartition V k)
    (top : V)
    (c : Fin k) :
    (localColourGraph P top c).IsBipartiteWith
      (localColourLeft P top c)
      (localColourRight P top c) := by
  constructor
  · rw [Set.disjoint_left]
    intro u huL huR
    simp [localColourLeft, localColourRight] at huL huR
  · intro u v huv
    have hdata :=
      (localColourGraph_adj P top c u v).1 huv
    have hbit :=
      bit_ne_of_localIncidentColor P
        (show u.1 ≠ v.1 by
          intro h
          apply hdata.1
          exact Subtype.ext h)
    rw [hdata.2] at hbit
    cases hu : P.bit u.1 c <;>
      cases hv : P.bit v.1 c <;>
      simp_all [localColourLeft, localColourRight]

theorem localColourGraph_isBipartite
    {V : Type*} [LinearOrder V] {k : ℕ}
    (P : BinaryEdgePartition V k)
    (top : V)
    (c : Fin k) :
    (localColourGraph P top c).IsBipartite :=
  (localColourGraph_isBipartiteWith P top c).isBipartite

/-- Every vertex in a colour-class support is active in that coordinate. -/
theorem localColourGraph_support_active
    {V : Type*} [LinearOrder V] [Fintype V] {k : ℕ}
    (P : BinaryEdgePartition V k)
    (top : V)
    (c : Fin k)
    (u : OtherVertex top)
    (hu : u ∈ (localColourGraph P top c).support) :
    c ∈ active P u.1 := by
  obtain ⟨v, huv⟩ := hu
  have hdata :=
    (localColourGraph_adj P top c u v).1 huv
  rw [← hdata.2]
  exact localIncidentColor_mem_active P
    (show u.1 ≠ v.1 by
      intro h
      apply hdata.1
      exact Subtype.ext h)

/-- If c is inactive at top, every non-top vertex active in c really lies in
the support of the c-colour graph on the five minima. -/
theorem active_mem_localColourGraph_support_of_not_top
    {V : Type*} [LinearOrder V] [Fintype V] {k : ℕ}
    (P : BinaryEdgePartition V k)
    (top : V)
    (c : Fin k)
    (hcTop : c ∉ active P top)
    (u : OtherVertex top)
    (hu : c ∈ active P u.1) :
    u ∈ (localColourGraph P top c).support := by
  classical
  simp only [active, Finset.mem_filter, Finset.mem_univ,
    true_and] at hu
  rcases hu with ⟨a, hau, hcol⟩ | ⟨w, huw, hcol⟩
  · have hat : a ≠ top := by
      intro h
      subst a
      apply hcTop
      simp only [active, Finset.mem_filter, Finset.mem_univ,
        true_and]
      exact Or.inr ⟨u.1, hau, hcol⟩
    let v : OtherVertex top := ⟨a, hat⟩
    refine ⟨v, ?_⟩
    apply (localColourGraph_adj P top c u v).2
    constructor
    · intro huv
      have hval := congrArg Subtype.val huv
      exact (ne_of_gt hau) hval.symm
    · unfold localIncidentColor
      have hnot : ¬ u.1 < a := not_lt_of_ge hau.le
      rw [dif_neg hnot]
      exact hcol
  · have hwt : w ≠ top := by
      intro h
      subst w
      apply hcTop
      simp only [active, Finset.mem_filter, Finset.mem_univ,
        true_and]
      exact Or.inl ⟨u.1, huw, hcol⟩
    let v : OtherVertex top := ⟨w, hwt⟩
    refine ⟨v, ?_⟩
    apply (localColourGraph_adj P top c u v).2
    constructor
    · intro huv
      have hval := congrArg Subtype.val huv
      exact (ne_of_lt huw) hval
    · unfold localIncidentColor
      rw [dif_pos huw]
      exact hcol

/-- Hence, off the top-active coordinates, support is exactly active incidence
restricted to the five minima. -/
theorem localColourGraph_support_iff_active_of_not_top
    {V : Type*} [LinearOrder V] [Fintype V] {k : ℕ}
    (P : BinaryEdgePartition V k)
    (top : V)
    (c : Fin k)
    (hcTop : c ∉ active P top)
    (u : OtherVertex top) :
    u ∈ (localColourGraph P top c).support ↔
      c ∈ active P u.1 := by
  constructor
  · exact localColourGraph_support_active P top c u
  · exact active_mem_localColourGraph_support_of_not_top
      P top c hcTop u

#print axioms localIncidentColor_comm
#print axioms bit_ne_of_localIncidentColor
#print axioms localColourGraph_isBipartiteWith
#print axioms localColourGraph_support_iff_active_of_not_top

end JSP000404Research
