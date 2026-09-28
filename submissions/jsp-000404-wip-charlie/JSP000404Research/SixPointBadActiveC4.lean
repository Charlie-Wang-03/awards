import JSP000404Research.SixPointMergedMonochromaticC4
import Mathlib.Tactic

/-!
# Every exceptional minimum is active in a monochromatic C4 colour

In the exact two-exception equality terminal the five minima have reduced
active-card profile

  3,3,2,2,2,

so total reduced colour incidence is 12 while the ten minimum-minimum edges
give total colour-class edge count 10.

Fix one exceptional minimum b.  It is active in exactly three reduced colours.

* If such a colour is C4-free, the five-minimum extremal lemma gives
    |E_c| + 1 <= |V_c|.
* If a reduced colour is not active at b, then its support uses at most the
  other four minima.  A bipartite graph on at most four active vertices has
    |E_c| <= |V_c|.

Hence if all three colours active at b were C4-free, summing over all reduced
colours would give

  10 + 3 <= 12,

impossible.  Therefore every exceptional minimum is active in at least one
reduced colour whose colour graph contains a C4.
-/

namespace JSP000404Research

open BinaryEdgePartition
open scoped BigOperators

/-- A bipartite graph with at most four active vertices has no more edges
than active vertices. -/
theorem bipartite_edge_card_le_active_card_of_active_card_le_four
    {W : Type*} [Fintype W]
    (G : SimpleGraph W)
    [DecidableRel G.Adj]
    (L R A : Finset W)
    (hbi : G.IsBipartiteWith (L : Set W) (R : Set W))
    (hsplit : L.card + R.card = A.card)
    (hA4 : A.card ≤ 4) :
    G.edgeFinset.card ≤ A.card := by
  classical
  have hdeg :=
    SimpleGraph.isBipartiteWith_sum_degrees_eq_card_edges hbi
  have hdegBound :
      (∑ u ∈ L, G.degree u) ≤
        ∑ _u ∈ L, R.card := by
    exact Finset.sum_le_sum
      (fun u hu =>
        SimpleGraph.isBipartiteWith_degree_le hbi hu)
  have hprod :
      G.edgeFinset.card ≤ L.card * R.card := by
    rw [hdeg] at hdegBound
    simpa [Nat.mul_comm] using hdegBound
  by_cases hL0 : L.card = 0
  · rw [hL0] at hprod
    simp at hprod
    omega
  by_cases hR0 : R.card = 0
  · rw [hR0] at hprod
    simp at hprod
    omega
  have hLpos : 1 ≤ L.card := by omega
  have hRpos : 1 ≤ R.card := by omega
  have hsum4 : L.card + R.card ≤ 4 := by
    rw [hsplit]
    exact hA4
  have hprodLe :
      L.card * R.card ≤ L.card + R.card := by
    interval_cases hL : L.card <;>
      interval_cases hR : R.card <;>
      omega
  rw [hsplit] at hprodLe
  exact hprod.trans hprodLe

/-- If a used non-root colour is inactive at one of the five minima, then its
edge count is at most its active-minimum count. -/
theorem localColourGraph_edge_card_le_active_of_inactive_minimum
    {V : Type*} [LinearOrder V] [Fintype V] {k : ℕ}
    (P : BinaryEdgePartition V k)
    (top : V)
    (root c : Fin k)
    (hcard : Fintype.card V = 6)
    (hcTop : c ∉ active P top)
    (bad : OtherVertex top)
    (hcBad : c ∉ active P bad.1) :
    (localColourGraph P top c).edgeFinset.card ≤
      (localColourActiveMinima P top c).card := by
  classical
  let A := localColourActiveMinima P top c
  let L := localColourLeftActiveMinima P top c
  let R := localColourRightActiveMinima P top c
  have hbi :
      (localColourGraph P top c).IsBipartiteWith
        (L : Set (OtherVertex top))
        (R : Set (OtherVertex top)) := by
    simpa [L, R] using
      localColourGraph_isBipartiteWith_active_split
        P top c hcTop
  have hsplit :
      L.card + R.card = A.card := by
    simpa [A, L, R] using
      localColour_active_split P top c
  have hsubset :
      A ⊆ (Finset.univ.erase bad : Finset (OtherVertex top)) := by
    intro u hu
    have huActive :
        c ∈ active P u.1 := by
      simpa [A, localColourActiveMinima] using hu
    have hubad : u ≠ bad := by
      intro h
      subst u
      exact hcBad huActive
    simp [hubad]
  have hA4 : A.card ≤ 4 := by
    have hle := Finset.card_le_card hsubset
    have hfive :
        Fintype.card (OtherVertex top) = 5 :=
      card_otherVertex_eq_five_of_card_six hcard top
    have hcomp :
        (Finset.univ.erase bad : Finset (OtherVertex top)).card = 4 := by
      rw [Finset.card_erase_of_mem (Finset.mem_univ bad),
          Finset.card_univ, hfive]
      norm_num
    rw [hcomp] at hle
    exact hle
  exact
    bipartite_edge_card_le_active_card_of_active_card_le_four
      (localColourGraph P top c) L R A hbi hsplit hA4

/-- In the exact reduced 3,3,2,2,2 profile, each bad minimum is active in some
non-root colour containing a four-cycle. -/
theorem bad_minimum_active_in_some_monochromatic_fourCycle
    {V : Type*} [LinearOrder V] [Fintype V] {k : ℕ}
    (P : BinaryEdgePartition V k)
    (top bad₁ bad₂ : V)
    (root : Fin k)
    (htb₁ : top ≠ bad₁)
    (htb₂ : top ≠ bad₂)
    (hb₁₂ : bad₁ ≠ bad₂)
    (hcard : Fintype.card V = 6)
    (hrootTop : active P top = {root})
    (hrootEdges :
      ∀ {u v : V}, u < v →
        u ≠ top → v ≠ top →
        P.edgeColor u v ≠ root)
    (hBad₁ : ((active P bad₁).erase root).card = 3)
    (hBad₂ : ((active P bad₂).erase root).card = 3)
    (hOther :
      ∀ v : V,
        v ≠ top → v ≠ bad₁ → v ≠ bad₂ →
        ((active P v).erase root).card = 2)
    (bad : V)
    (hbadCase : bad = bad₁ ∨ bad = bad₂) :
    ∃ c : Fin k,
      c ≠ root ∧
      c ∈ active P bad ∧
      HasFourCycle (localColourGraph P top c) := by
  classical
  let U := reducedUsedColours P top root
  let B : OtherVertex top :=
    ⟨bad, by
      rcases hbadCase with rfl | rfl
      · exact htb₁.symm
      · exact htb₂.symm⟩

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
      _ = 12 := by
        exact
          sum_reduced_active_card_eq_twelve
            P top bad₁ bad₂ root
            htb₁ htb₂ hb₁₂ hcard
            hBad₁ hBad₂ hOther

  have hBadCard :
      ((active P bad).erase root).card = 3 := by
    rcases hbadCase with rfl | rfl
    · exact hBad₁
    · exact hBad₂

  by_contra hnone
  push_neg at hnone

  have hterm :
      ∀ c ∈ U,
        (localColourGraph P top c).edgeFinset.card +
            (if c ∈ active P bad then 1 else 0)
          ≤
        (localColourActiveMinima P top c).card := by
    intro c hcU
    have hcData :=
      (mem_reducedUsedColours P top root c).1
        (by simpa [U] using hcU)
    have hcTop : c ∉ active P top := by
      rw [hrootTop]
      simp [hcData.1]
    by_cases hcb : c ∈ active P bad
    · have hnoC4 : ¬ HasFourCycle (localColourGraph P top c) := by
        exact hnone c hcData.1 hcb
      have hlt :=
        localColourGraph_edge_card_lt_active_of_no_fourCycle
          P top c hcard hcTop hcData.2 hnoC4
      simp [hcb]
      omega
    · have hle :=
        localColourGraph_edge_card_le_active_of_inactive_minimum
          P top root c hcard hcTop B (by simpa [B] using hcb)
      simp [hcb]
      exact hle

  have hsum :
      (∑ c ∈ U,
        ((localColourGraph P top c).edgeFinset.card +
          (if c ∈ active P bad then 1 else 0)))
        ≤
      ∑ c ∈ U,
        (localColourActiveMinima P top c).card :=
    Finset.sum_le_sum hterm

  have hIndicator :
      (∑ c ∈ U, (if c ∈ active P bad then 1 else 0)) = 3 := by
    have hsetEq :
        U.filter (fun c => c ∈ active P bad) =
          (active P bad).erase root := by
      ext c
      simp only [Finset.mem_filter, Finset.mem_erase]
      constructor
      · rintro ⟨hcU, hcb⟩
        exact ⟨(mem_reducedUsedColours P top root c).1 hcU |>.1,
          hcb⟩
      · rintro ⟨hcr, hcb⟩
        have htopNe : bad ≠ top := by
          rcases hbadCase with rfl | rfl
          · exact htb₁.symm
          · exact htb₂.symm
        let bsub : OtherVertex top := ⟨bad, htopNe⟩
        exact ⟨
          active_nonroot_mem_reducedUsedColours
            P top root c bsub hcr hcb,
          hcb⟩
    calc
      (∑ c ∈ U, (if c ∈ active P bad then 1 else 0))
          = (U.filter (fun c => c ∈ active P bad)).card := by
              simp
      _ = ((active P bad).erase root).card := by rw [hsetEq]
      _ = 3 := hBadCard

  have hleft :
      (∑ c ∈ U,
        ((localColourGraph P top c).edgeFinset.card +
          (if c ∈ active P bad then 1 else 0)))
        =
      (∑ c ∈ U,
        (localColourGraph P top c).edgeFinset.card) +
      (∑ c ∈ U,
        (if c ∈ active P bad then 1 else 0)) := by
    rw [Finset.sum_add_distrib]

  rw [hleft, hEdgeSum, hIndicator, hActiveSum] at hsum
  omega

#print axioms bipartite_edge_card_le_active_card_of_active_card_le_four
#print axioms localColourGraph_edge_card_le_active_of_inactive_minimum
#print axioms bad_minimum_active_in_some_monochromatic_fourCycle

end JSP000404Research
