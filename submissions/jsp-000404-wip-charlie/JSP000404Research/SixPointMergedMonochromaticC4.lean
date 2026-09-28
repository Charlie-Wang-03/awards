import JSP000404Research.FiveMinimaC4Extremal
import JSP000404Research.SixPointMergedEqualityRoot
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Combinatorics.Enumerative.DoubleCounting
import Mathlib.Tactic

/-!
# A monochromatic four-cycle in the two-exception equality terminal

After removing the unique top root colour, the five minima have exact reduced
active-card profile

  3, 3, 2, 2, 2.

Thus the total reduced colour incidence is 12, while the complete graph on
the five minima has 10 edges.  Every reduced colour class is bipartite.

Let U be the set of used non-root colours.  The two exceptional minima already
show |U| >= 3.  If every colour class were C4-free, the five-minimum extremal
lemma gives

  |E_c| + 1 <= |V_c|

for every c in U.  Summing over c gives

  10 + |U| <= 12,

contradicting |U| >= 3.

Therefore some non-root merged colour contains a genuine four-cycle among the
five minima.
-/

namespace JSP000404Research

open BinaryEdgePartition
open scoped BigOperators

noncomputable def reducedUsedColours
    {V : Type*} [LinearOrder V] [Fintype V] {k : ℕ}
    (P : BinaryEdgePartition V k)
    (top : V)
    (root : Fin k) : Finset (Fin k) :=
  Finset.univ.filter fun c =>
    c ≠ root ∧ (localColourActiveMinima P top c).Nonempty

theorem mem_reducedUsedColours
    {V : Type*} [LinearOrder V] [Fintype V] {k : ℕ}
    (P : BinaryEdgePartition V k)
    (top : V)
    (root c : Fin k) :
    c ∈ reducedUsedColours P top root ↔
      c ≠ root ∧ (localColourActiveMinima P top c).Nonempty := by
  simp [reducedUsedColours]

theorem active_nonroot_mem_reducedUsedColours
    {V : Type*} [LinearOrder V] [Fintype V] {k : ℕ}
    (P : BinaryEdgePartition V k)
    (top : V)
    (root c : Fin k)
    (u : OtherVertex top)
    (hcr : c ≠ root)
    (hcu : c ∈ active P u.1) :
    c ∈ reducedUsedColours P top root := by
  rw [mem_reducedUsedColours]
  refine ⟨hcr, ?_⟩
  exact ⟨u, by
    simp [localColourActiveMinima, hcu]⟩

theorem sum_reducedUsedColours_degree_eq_four
    {V : Type*} [LinearOrder V] [Fintype V] {k : ℕ}
    (P : BinaryEdgePartition V k)
    (top : V)
    (root : Fin k)
    (hcard : Fintype.card V = 6)
    (hrootEdges :
      ∀ {u v : V}, u < v →
        u ≠ top → v ≠ top →
        P.edgeColor u v ≠ root)
    (u : OtherVertex top) :
    (∑ c ∈ reducedUsedColours P top root,
      (localColourGraph P top c).degree u) = 4 := by
  classical
  let U := reducedUsedColours P top root
  let N : Finset (OtherVertex top) := Finset.univ.erase u
  let g : OtherVertex top → Fin k :=
    fun v => localIncidentColor P u.1 v.1

  have hmaps : (N : Set (OtherVertex top)).MapsTo g U := by
    intro v hv
    have hvdata := Finset.mem_erase.mp hv
    have hvu : v ≠ u := hvdata.1
    have hval : v.1 ≠ u.1 := by
      intro h
      exact hvu (Subtype.ext h)
    have hroot :
        g v ≠ root := by
      dsimp [g]
      exact localIncidentColor_ne_root_of_nonTop
        P u.2 v.2 hval.symm hrootEdges
    have hactive :
        g v ∈ active P u.1 := by
      dsimp [g]
      exact localIncidentColor_mem_active P hval.symm
    exact active_nonroot_mem_reducedUsedColours
      P top root (g v) u hroot hactive

  have hfib :
      N.card =
        ∑ c ∈ U, #{v ∈ N | g v = c} :=
    Finset.card_eq_sum_card_fiberwise hmaps

  have hfiberDegree :
      ∀ c ∈ U,
        #{v ∈ N | g v = c} =
          (localColourGraph P top c).degree u := by
    intro c hc
    rw [← SimpleGraph.card_neighborFinset_eq_degree,
        localColourGraph_neighborFinset]
    rfl

  have hNcard : N.card = 4 := by
    dsimp [N]
    rw [Finset.card_erase_of_mem (Finset.mem_univ u)]
    rw [Finset.card_univ,
      card_otherVertex_eq_five_of_card_six hcard top]
    norm_num

  calc
    (∑ c ∈ reducedUsedColours P top root,
      (localColourGraph P top c).degree u)
        =
      ∑ c ∈ U, #{v ∈ N | g v = c} := by
        apply Finset.sum_congr rfl
        intro c hc
        exact (hfiberDegree c hc).symm
    _ = N.card := hfib.symm
    _ = 4 := hNcard

theorem sum_reducedUsedColours_edge_card_eq_ten
    {V : Type*} [LinearOrder V] [Fintype V] {k : ℕ}
    (P : BinaryEdgePartition V k)
    (top : V)
    (root : Fin k)
    (hcard : Fintype.card V = 6)
    (hrootEdges :
      ∀ {u v : V}, u < v →
        u ≠ top → v ≠ top →
        P.edgeColor u v ≠ root) :
    (∑ c ∈ reducedUsedColours P top root,
      (localColourGraph P top c).edgeFinset.card) = 10 := by
  classical
  let U := reducedUsedColours P top root
  have hsumVertex :
      (∑ u : OtherVertex top,
        ∑ c ∈ U, (localColourGraph P top c).degree u)
        = 20 := by
    calc
      (∑ u : OtherVertex top,
        ∑ c ∈ U, (localColourGraph P top c).degree u)
          = ∑ _u : OtherVertex top, 4 := by
              apply Finset.sum_congr rfl
              intro u _
              exact sum_reducedUsedColours_degree_eq_four
                P top root hcard hrootEdges u
      _ = Fintype.card (OtherVertex top) * 4 := by simp
      _ = 20 := by
            rw [card_otherVertex_eq_five_of_card_six hcard top]
            norm_num

  have htwice :
      2 * (∑ c ∈ U,
        (localColourGraph P top c).edgeFinset.card) = 20 := by
    calc
      2 * (∑ c ∈ U,
        (localColourGraph P top c).edgeFinset.card)
          =
        ∑ c ∈ U,
          2 * (localColourGraph P top c).edgeFinset.card := by
            rw [Finset.mul_sum]
      _ =
        ∑ c ∈ U,
          ∑ u : OtherVertex top,
            (localColourGraph P top c).degree u := by
            apply Finset.sum_congr rfl
            intro c hc
            rw [SimpleGraph.sum_degrees_eq_twice_card_edges]
      _ =
        ∑ u : OtherVertex top,
          ∑ c ∈ U,
            (localColourGraph P top c).degree u := by
            rw [Finset.sum_comm]
      _ = 20 := hsumVertex

  omega

theorem usedColour_active_below_eq_erase
    {V : Type*} [LinearOrder V] [Fintype V] {k : ℕ}
    (P : BinaryEdgePartition V k)
    (top : V)
    (root : Fin k)
    (u : OtherVertex top) :
    (reducedUsedColours P top root).bipartiteBelow
        (fun c v : OtherVertex top => c ∈ active P v.1) u
      =
    (active P u.1).erase root := by
  classical
  ext c
  simp only [Finset.mem_bipartiteBelow,
    Finset.mem_erase]
  constructor
  · rintro ⟨hcU, hcu⟩
    exact ⟨(mem_reducedUsedColours P top root c).1 hcU |>.1,
      hcu⟩
  · rintro ⟨hcr, hcu⟩
    exact ⟨active_nonroot_mem_reducedUsedColours
      P top root c u hcr hcu, hcu⟩

theorem sum_reducedUsedColours_active_card_eq
    {V : Type*} [LinearOrder V] [Fintype V] {k : ℕ}
    (P : BinaryEdgePartition V k)
    (top : V)
    (root : Fin k) :
    (∑ c ∈ reducedUsedColours P top root,
      (localColourActiveMinima P top c).card)
      =
    ∑ u : OtherVertex top, ((active P u.1).erase root).card := by
  classical
  let U := reducedUsedColours P top root
  let r : Fin k → OtherVertex top → Prop :=
    fun c u => c ∈ active P u.1
  calc
    (∑ c ∈ reducedUsedColours P top root,
      (localColourActiveMinima P top c).card)
        =
      ∑ c ∈ U, #(Finset.univ.bipartiteAbove r c) := by
        apply Finset.sum_congr rfl
        intro c hc
        rfl
    _ =
      ∑ u ∈ (Finset.univ : Finset (OtherVertex top)),
        #(U.bipartiteBelow r u) := by
        exact Finset.sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow
    _ =
      ∑ u ∈ (Finset.univ : Finset (OtherVertex top)),
        ((active P u.1).erase root).card := by
        apply Finset.sum_congr rfl
        intro u hu
        rw [usedColour_active_below_eq_erase P top root u]
    _ =
      ∑ u : OtherVertex top,
        ((active P u.1).erase root).card := by simp

theorem sum_reduced_active_card_eq_twelve
    {V : Type*} [LinearOrder V] [Fintype V] {k : ℕ}
    (P : BinaryEdgePartition V k)
    (top bad₁ bad₂ : V)
    (root : Fin k)
    (htb₁ : top ≠ bad₁)
    (htb₂ : top ≠ bad₂)
    (hb₁₂ : bad₁ ≠ bad₂)
    (hcard : Fintype.card V = 6)
    (hBad₁ : ((active P bad₁).erase root).card = 3)
    (hBad₂ : ((active P bad₂).erase root).card = 3)
    (hOther :
      ∀ v : V,
        v ≠ top → v ≠ bad₁ → v ≠ bad₂ →
        ((active P v).erase root).card = 2) :
    (∑ u : OtherVertex top,
      ((active P u.1).erase root).card) = 12 := by
  classical
  let b₁ : OtherVertex top := ⟨bad₁, htb₁.symm⟩
  let b₂ : OtherVertex top := ⟨bad₂, htb₂.symm⟩
  let S : Finset (OtherVertex top) :=
    (Finset.univ.erase b₁).erase b₂

  have hb₁₂' : b₁ ≠ b₂ := by
    intro h
    apply hb₁₂
    exact congrArg Subtype.val h

  have hb₁Mem :
      b₁ ∈ (Finset.univ : Finset (OtherVertex top)) := by simp
  have hb₂Mem :
      b₂ ∈ (Finset.univ.erase b₁ : Finset (OtherVertex top)) := by
    simp [hb₁₂'.symm]

  have hScard : S.card = 3 := by
    dsimp [S]
    rw [Finset.card_erase_of_mem hb₂Mem,
        Finset.card_erase_of_mem hb₁Mem,
        Finset.card_univ,
        card_otherVertex_eq_five_of_card_six hcard top]
    norm_num

  have hSsum :
      (∑ u ∈ S, ((active P u.1).erase root).card) = 6 := by
    calc
      (∑ u ∈ S, ((active P u.1).erase root).card)
          = ∑ _u ∈ S, 2 := by
              apply Finset.sum_congr rfl
              intro u hu
              have hudata := Finset.mem_erase.mp hu
              have hudata2 := Finset.mem_erase.mp hudata.2
              have hut : u.1 ≠ top := u.2
              have hub₁ : u.1 ≠ bad₁ := by
                intro h
                apply hudata2.1
                apply Subtype.ext
                exact h
              have hub₂ : u.1 ≠ bad₂ := by
                intro h
                apply hudata.1
                apply Subtype.ext
                exact h
              exact hOther u.1 hut hub₁ hub₂
      _ = S.card * 2 := by simp [Nat.mul_comm]
      _ = 6 := by rw [hScard]; norm_num

  have hdecomp :
      (∑ u : OtherVertex top,
        ((active P u.1).erase root).card)
        =
      ((active P bad₁).erase root).card +
      ((active P bad₂).erase root).card +
      ∑ u ∈ S, ((active P u.1).erase root).card := by
    dsimp [S, b₁, b₂]
    rw [← Finset.sum_erase_add
        (fun u : OtherVertex top =>
          ((active P u.1).erase root).card)
        hb₁Mem]
    rw [← Finset.sum_erase_add
        (fun u : OtherVertex top =>
          ((active P u.1).erase root).card)
        hb₂Mem]
    omega

  rw [hdecomp, hBad₁, hBad₂, hSsum]
  norm_num

theorem reducedUsedColours_card_ge_three
    {V : Type*} [LinearOrder V] [Fintype V] {k : ℕ}
    (P : BinaryEdgePartition V k)
    (top bad : V)
    (root : Fin k)
    (htb : top ≠ bad)
    (hBad : ((active P bad).erase root).card = 3) :
    3 ≤ (reducedUsedColours P top root).card := by
  classical
  let b : OtherVertex top := ⟨bad, htb.symm⟩
  have hsub :
      (active P bad).erase root ⊆
        reducedUsedColours P top root := by
    intro c hc
    have hcdata := Finset.mem_erase.mp hc
    exact active_nonroot_mem_reducedUsedColours
      P top root c b hcdata.1 hcdata.2
  have hle := Finset.card_le_card hsub
  rw [hBad] at hle
  exact hle

/-- Main pure combinatorial terminal: exact two-exception equality forces a
non-root monochromatic C4 among the five minima. -/
theorem six_point_two_exception_has_monochromatic_fourCycle
    {V : Type*} [LinearOrder V] [Fintype V]
    {n : ℕ}
    (hn : 4 ≤ n)
    (P : BinaryEdgePartition V n)
    (top bad₁ bad₂ : V)
    (htb₁ : top ≠ bad₁)
    (htb₂ : top ≠ bad₂)
    (hb₁₂ : bad₁ ≠ bad₂)
    (hcard : Fintype.card V = 6)
    (hTop : (active P top).card ≤ 1)
    (hBad₁ : (active P bad₁).card ≤ 4)
    (hBad₂ : (active P bad₂).card ≤ 4)
    (hOther :
      ∀ v : V,
        v ≠ top → v ≠ bad₁ → v ≠ bad₂ →
        (active P v).card ≤ 3) :
    ∃ root c : Fin n,
      c ≠ root ∧
      HasFourCycle (localColourGraph P top c) := by
  classical
  obtain ⟨root, hrootTop, hrootAll, hrootEdges,
      hrootBad₁, hrootBad₂, hrootOther⟩ :=
    six_point_two_exception_root_factorization
      hn P top bad₁ bad₂ htb₁ htb₂ hb₁₂ hcard
      hTop hBad₁ hBad₂ hOther

  let U := reducedUsedColours P top root

  have hEdgeSum :
      (∑ c ∈ U,
        (localColourGraph P top c).edgeFinset.card) = 10 := by
    simpa [U] using
      sum_reducedUsedColours_edge_card_eq_ten
        P top root hcard hrootEdges

  have hActiveSum :
      (∑ c ∈ U,
        (localColourActiveMinima P top c).card) = 12 := by
    calc
      (∑ c ∈ U,
        (localColourActiveMinima P top c).card)
          =
        ∑ u : OtherVertex top,
          ((active P u.1).erase root).card := by
            simpa [U] using
              sum_reducedUsedColours_active_card_eq
                P top root
      _ = 12 :=
        sum_reduced_active_card_eq_twelve
          P top bad₁ bad₂ root
          htb₁ htb₂ hb₁₂ hcard
          hrootBad₁ hrootBad₂ hrootOther

  have hU3 : 3 ≤ U.card := by
    simpa [U] using
      reducedUsedColours_card_ge_three
        P top bad₁ root htb₁ hrootBad₁

  by_contra hnone
  push_neg at hnone
  have hloss :
      ∀ c ∈ U,
        (localColourGraph P top c).edgeFinset.card + 1 ≤
          (localColourActiveMinima P top c).card := by
    intro c hc
    have hcdata :=
      (mem_reducedUsedColours P top root c).1
        (by simpa [U] using hc)
    have hcTop : c ∉ active P top := by
      rw [hrootTop]
      simp [hcdata.1]
    have hlt :=
      localColourGraph_edge_card_lt_active_of_no_fourCycle
        P top c hcard hcTop hcdata.2 (hnone root c hcdata.1)
    omega

  have hsumLoss :
      (∑ c ∈ U,
        ((localColourGraph P top c).edgeFinset.card + 1))
        ≤
      ∑ c ∈ U,
        (localColourActiveMinima P top c).card :=
    Finset.sum_le_sum hloss

  have hleft :
      (∑ c ∈ U,
        ((localColourGraph P top c).edgeFinset.card + 1))
        =
      (∑ c ∈ U,
        (localColourGraph P top c).edgeFinset.card) + U.card := by
    rw [Finset.sum_add_distrib]
    simp

  rw [hleft, hEdgeSum, hActiveSum] at hsumLoss
  omega

#print axioms sum_reducedUsedColours_degree_eq_four
#print axioms sum_reducedUsedColours_edge_card_eq_ten
#print axioms sum_reducedUsedColours_active_card_eq
#print axioms six_point_two_exception_has_monochromatic_fourCycle

end JSP000404Research
