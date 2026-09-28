import JSP000404Research.FiveMinimaC4Pendant
import JSP000404Research.FiveMinimaColourGraph
import JSP000404Research.CutMonochromaticC4Angles
import Mathlib.Tactic

/-!
# Repeated non-C4 colour at a pendant exceptional minimum

Fix a non-root colour c0 whose five-minimum colour graph contains a C4.
Suppose an exceptional minimum b is active in c0 but lies on no c0-coloured
C4.  Bipartiteness and the five-vertex C4 pendant theorem force b to have
c0-degree exactly one.

At the exact two-exception equality terminal, b has exactly three reduced
(non-root) active colours, and all of them occur on its four minimum-minimum
incident edges.  Hence the colour image of those four edges has cardinality
three.  Two incident edges repeat a colour.  The repeated colour cannot be c0,
because c0 has degree one at b.

At a saturation-bad centre, equal merged incident colours lift to equal old
cut bands, so the repeated pair gives a strict sub-lambda angle.
-/

namespace JSP000404Research

open BinaryEdgePartition

theorem pendant_bad_has_repeated_nonC4_colour
    {V : Type*} [LinearOrder V] [Fintype V]
    {k : ℕ}
    (P : BinaryEdgePartition V k)
    (top bad : V)
    (root c0 : Fin k)
    (hbt : bad ≠ top)
    (hcard : Fintype.card V = 6)
    (hrootTop : active P top = {root})
    (hrootEdges :
      ∀ {u v : V}, u < v →
        u ≠ top → v ≠ top →
        P.edgeColor u v ≠ root)
    (hc0root : c0 ≠ root)
    (hReduced : ((active P bad).erase root).card = 3)
    (hc0Bad : c0 ∈ active P bad)
    (hC4 : HasFourCycle (localColourGraph P top c0))
    (hnoBadC4 :
      ¬ ∃ u v w : OtherVertex top,
        (⟨bad, hbt⟩ : OtherVertex top) ≠ u ∧
        u ≠ v ∧ v ≠ w ∧
        w ≠ (⟨bad, hbt⟩ : OtherVertex top) ∧
        (⟨bad, hbt⟩ : OtherVertex top) ≠ v ∧
        u ≠ w ∧
        (localColourGraph P top c0).Adj
          (⟨bad, hbt⟩ : OtherVertex top) u ∧
        (localColourGraph P top c0).Adj u v ∧
        (localColourGraph P top c0).Adj v w ∧
        (localColourGraph P top c0).Adj w
          (⟨bad, hbt⟩ : OtherVertex top)) :
    ∃ x y : V,
      x ≠ top ∧ x ≠ bad ∧
      y ≠ top ∧ y ≠ bad ∧
      x ≠ y ∧
      localIncidentColor P bad x =
        localIncidentColor P bad y ∧
      localIncidentColor P bad x ≠ c0 := by
  classical
  let B : OtherVertex top := ⟨bad, hbt⟩
  let G := localColourGraph P top c0

  have hc0Top : c0 ∉ active P top := by
    rw [hrootTop]
    simp [hc0root]
  have hBSupp : B ∈ G.support := by
    dsimp [G, B]
    exact active_mem_localColourGraph_support_of_not_top
      P top c0 hc0Top ⟨bad, hbt⟩ hc0Bad

  obtain ⟨a,b,c,d,hab,hbc,hcd,hda,hac,hbd,
      habE,hbcE,hcdE,hdaE⟩ := hC4

  have hbadA : B ≠ a := by
    intro h
    subst a
    apply hnoBadC4
    exact ⟨b,c,d,hab,hbc,hcd,hda,hac,hbd,
      habE,hbcE,hcdE,hdaE⟩
  have hbadB : B ≠ b := by
    intro h
    subst b
    apply hnoBadC4
    exact ⟨c,d,a,hbc,hcd,hda,hab.symm,hbd,hac.symm,
      hbcE,hcdE,hdaE,habE.symm⟩
  have hbadC : B ≠ c := by
    intro h
    subst c
    apply hnoBadC4
    exact ⟨d,a,b,hcd,hda,hab,hbc.symm,hac.symm,hbd.symm,
      hcdE,hdaE,habE,hbcE.symm⟩
  have hbadD : B ≠ d := by
    intro h
    subst d
    apply hnoBadC4
    exact ⟨a,b,c,hda,hab,hbc,hcd.symm,hbd.symm,hac,
      hdaE,habE,hbcE,hcdE.symm⟩

  have hdeg : G.degree B = 1 := by
    apply degree_eq_one_of_active_off_fourCycle_no_cycle_through
      G
      (card_otherVertex_eq_five_of_card_six hcard top)
      (localColourGraph_isBipartite P top c0)
      hab hbc hcd hda hac hbd
      habE hbcE hcdE hdaE
      hbadA hbadB hbadC hbadD
      hBSupp
    exact hnoBadC4

  let S : Finset V := ((Finset.univ.erase top).erase bad)
  have hbadMem :
      bad ∈ (Finset.univ.erase top : Finset V) := by
    simp [hbt]
  have hScard : S.card = 4 := by
    dsimp [S]
    rw [Finset.card_erase_of_mem hbadMem,
        Finset.card_erase_of_mem (Finset.mem_univ top)]
    simp [hcard]

  let f : V → Fin k := fun x => localIncidentColor P bad x

  have himageSub :
      S.image f ⊆ (active P bad).erase root := by
    intro q hq
    obtain ⟨x,hxS,rfl⟩ := Finset.mem_image.mp hq
    have hxBad := (Finset.mem_erase.mp hxS).1
    have hxTop := (Finset.mem_erase.mp (Finset.mem_erase.mp hxS).2).1
    apply Finset.mem_erase.mpr
    exact ⟨
      localIncidentColor_ne_root_of_nonTop
        P hbt hxTop hxBad.symm hrootEdges,
      localIncidentColor_mem_active P hxBad.symm⟩

  have hactiveSub :
      (active P bad).erase root ⊆ S.image f := by
    intro q hq
    have hqData := Finset.mem_erase.mp hq
    have hqTop : q ∉ active P top := by
      rw [hrootTop]
      simp [hqData.1]
    let B0 : OtherVertex top := ⟨bad, hbt⟩
    have hSupp :
        B0 ∈ (localColourGraph P top q).support :=
      active_mem_localColourGraph_support_of_not_top
        P top q hqTop B0 hqData.2
    obtain ⟨X,hBX⟩ := hSupp
    have hdata :=
      (localColourGraph_adj P top q B0 X).1 hBX
    let x : V := X.1
    have hxTop : x ≠ top := X.2
    have hxBad : x ≠ bad := by
      intro h
      apply hdata.1
      apply Subtype.ext
      exact h
    have hxS : x ∈ S := by
      simp [S, hxTop, hxBad]
    apply Finset.mem_image.mpr
    refine ⟨x,hxS,?_⟩
    simpa [f,B0,x] using hdata.2

  have himageEq :
      S.image f = (active P bad).erase root :=
    Finset.Subset.antisymm himageSub hactiveSub
  have himageCard : (S.image f).card = 3 := by
    rw [himageEq, hReduced]

  have hrepeat :
      ∃ x ∈ S, ∃ y ∈ S, x ≠ y ∧ f x = f y := by
    by_contra hnone
    push_neg at hnone
    have hinj : Set.InjOn f (S : Set V) := by
      intro x hx y hy hxy
      by_contra hne
      exact (hnone x hx y hy hne) hxy
    have hcardImage :
        (S.image f).card = S.card :=
      Finset.card_image_iff.mpr hinj
    rw [himageCard, hScard] at hcardImage
    omega

  obtain ⟨x,hxS,y,hyS,hxy,hfxy⟩ := hrepeat

  have hnotC0 : f x ≠ c0 := by
    intro hxc0
    have hyc0 : f y = c0 := by rw [← hfxy, hxc0]
    let X : OtherVertex top :=
      ⟨x, (Finset.mem_erase.mp (Finset.mem_erase.mp hxS).2).1⟩
    let Y : OtherVertex top :=
      ⟨y, (Finset.mem_erase.mp (Finset.mem_erase.mp hyS).2).1⟩
    have hXB : X ∈ G.neighborFinset B := by
      rw [SimpleGraph.mem_neighborFinset]
      apply (localColourGraph_adj P top c0 B X).2
      constructor
      · intro h
        have hv := congrArg Subtype.val h
        exact (Finset.mem_erase.mp hxS).1 hv.symm
      · simpa [B,G,X,f] using hxc0
    have hYB : Y ∈ G.neighborFinset B := by
      rw [SimpleGraph.mem_neighborFinset]
      apply (localColourGraph_adj P top c0 B Y).2
      constructor
      · intro h
        have hv := congrArg Subtype.val h
        exact (Finset.mem_erase.mp hyS).1 hv.symm
      · simpa [B,G,Y,f] using hyc0
    have hXY : X ≠ Y := by
      intro h
      apply hxy
      exact congrArg Subtype.val h
    have htwo : 2 ≤ (G.neighborFinset B).card :=
      Finset.two_le_card.mpr ⟨X,hXB,Y,hYB,hXY⟩
    rw [SimpleGraph.card_neighborFinset_eq_degree, hdeg] at htwo
    omega

  exact ⟨x,y,
    (Finset.mem_erase.mp (Finset.mem_erase.mp hxS).2).1,
    (Finset.mem_erase.mp hxS).1,
    (Finset.mem_erase.mp (Finset.mem_erase.mp hyS).2).1,
    (Finset.mem_erase.mp hyS).1,
    hxy,hfxy,hnotC0⟩

/-- Geometric application: at a saturation-bad pendant exceptional minimum,
the repeated non-C4 colour gives a strict sub-lambda angle. -/
theorem pendant_saturation_bad_has_repeated_small_angle
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane} (hp : Function.Injective p)
    (hcap : AngleCap p lam)
    (C : ∀ v : V, CentreProjectiveCycle hp v)
    {lam t delta c : ℝ} {n : ℕ}
    (hn : 1 ≤ n)
    (htpos : 0 < t)
    (hlam : lam = Real.pi / t)
    (ht : t = (n : ℝ) + delta)
    (hdelta0 : 0 ≤ delta)
    (hdeltaHalf : delta < (1 : ℝ) / 2)
    (hc0 : 0 ≤ c) (hcpi : c < Real.pi)
    (huncovered :
      ∀ u : GlobalUnitGapSlot C t,
        ¬ GlobalCyclicCriticalUnitBadAt
          C t delta u (t * c / Real.pi))
    (top bad : V)
    (root c0 : Fin n)
    (hbt : bad ≠ top)
    (hcard : Fintype.card V = 6)
    (hrootTop :
      active
        (uncoveredCutMergedPartition
          hp hcap C hn htpos hlam ht hdelta0
          hdeltaHalf hc0 hcpi huncovered)
        top = {root})
    (hrootEdges :
      ∀ {u v : V}, u < v →
        u ≠ top → v ≠ top →
        (uncoveredCutMergedPartition
          hp hcap C hn htpos hlam ht hdelta0
          hdeltaHalf hc0 hcpi huncovered).edgeColor u v ≠ root)
    (hc0root : c0 ≠ root)
    (hReduced :
      ((active
        (uncoveredCutMergedPartition
          hp hcap C hn htpos hlam ht hdelta0
          hdeltaHalf hc0 hcpi huncovered)
        bad).erase root).card = 3)
    (hc0Bad :
      c0 ∈ active
        (uncoveredCutMergedPartition
          hp hcap C hn htpos hlam ht hdelta0
          hdeltaHalf hc0 hcpi huncovered)
        bad)
    (hC4 :
      HasFourCycle
        (localColourGraph
          (uncoveredCutMergedPartition
            hp hcap C hn htpos hlam ht hdelta0
            hdeltaHalf hc0 hcpi huncovered)
          top c0))
    (hnoBadC4 :
      ¬ ∃ u v w : OtherVertex top,
        (⟨bad, hbt⟩ : OtherVertex top) ≠ u ∧
        u ≠ v ∧ v ≠ w ∧
        w ≠ (⟨bad, hbt⟩ : OtherVertex top) ∧
        (⟨bad, hbt⟩ : OtherVertex top) ≠ v ∧
        u ≠ w ∧
        (localColourGraph
          (uncoveredCutMergedPartition
            hp hcap C hn htpos hlam ht hdelta0
            hdeltaHalf hc0 hcpi huncovered)
          top c0).Adj (⟨bad,hbt⟩ : OtherVertex top) u ∧
        (localColourGraph
          (uncoveredCutMergedPartition
            hp hcap C hn htpos hlam ht hdelta0
            hdeltaHalf hc0 hcpi huncovered)
          top c0).Adj u v ∧
        (localColourGraph
          (uncoveredCutMergedPartition
            hp hcap C hn htpos hlam ht hdelta0
            hdeltaHalf hc0 hcpi huncovered)
          top c0).Adj v w ∧
        (localColourGraph
          (uncoveredCutMergedPartition
            hp hcap C hn htpos hlam ht hdelta0
            hdeltaHalf hc0 hcpi huncovered)
          top c0).Adj w (⟨bad,hbt⟩ : OtherVertex top))
    (hbad :
      CutSaturationBadAt
        hp hcap C htpos hlam ht hdelta0
        (by linarith : delta < 1)
        hc0 hcpi bad) :
    ∃ x y : V,
      x ≠ top ∧ x ≠ bad ∧
      y ≠ top ∧ y ≠ bad ∧
      x ≠ y ∧
      EuclideanGeometry.angle (p x) (p bad) (p y) < lam := by
  let M :=
    uncoveredCutMergedPartition
      hp hcap C hn htpos hlam ht hdelta0
      hdeltaHalf hc0 hcpi huncovered
  obtain ⟨x,y,hxt,hxb,hyt,hyb,hxy,heq,_hneC4⟩ :=
    pendant_bad_has_repeated_nonC4_colour
      M top bad root c0 hbt hcard
      hrootTop hrootEdges hc0root
      hReduced hc0Bad hC4 hnoBadC4
  refine ⟨x,y,hxt,hxb,hyt,hyb,hxy,?_⟩
  exact
    actual_angle_lt_lam_of_equal_uncovered_merged_color_at_saturation_bad
      hp hcap C hn htpos hlam ht hdelta0 hdeltaHalf
      hc0 hcpi huncovered
      bad x y
      hxb hyb hxy hbad
      (by simpa [M] using heq)

#print axioms pendant_bad_has_repeated_nonC4_colour
#print axioms pendant_saturation_bad_has_repeated_small_angle

end JSP000404Research
