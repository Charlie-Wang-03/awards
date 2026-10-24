import JSP000404Research.CutMonochromaticC4Angles
import JSP000404Research.SixPointMergedMonochromaticC4
import Mathlib.Tactic

/-!
# Bad-minimum incidence in the forced monochromatic C4

The two-exception equality terminal forces a monochromatic four-cycle on four
of the five minima.  Since there are only five minima total and the two bad
minima are distinct, at least one bad minimum must lie on that four-cycle.

Combining this elementary incidence fact with CutMonochromaticC4Angles gives
a concrete geometric consequence: at least one bad minimum has a strict
sub-lambda angle between its two cycle neighbours.  If both bad minima lie on
the cycle, both receive such an angle.
-/

namespace JSP000404Research

open BinaryEdgePartition

-- The fully expanded eight-way subtype/angle case analysis is expensive to
-- elaborate. This increases the compiler budget only, not proof strength.
set_option maxHeartbeats 10000000

theorem one_of_two_distinct_vertices_mem_fourCycle_vertices
    {W : Type*} [Fintype W] [DecidableEq W]
    (hcard : Fintype.card W = 5)
    {bad₁ bad₂ a b c d : W}
    (hbad : bad₁ ≠ bad₂)
    (hab : a ≠ b) (hbc : b ≠ c)
    (hcd : c ≠ d) (hda : d ≠ a)
    (hac : a ≠ c) (hbd : b ≠ d) :
    bad₁ ∈ ({a,b,c,d} : Finset W) ∨
      bad₂ ∈ ({a,b,c,d} : Finset W) := by
  classical
  let S : Finset W := {a,b,c,d}
  have hScard : S.card = 4 := by
    dsimp [S]
    simp [hab, hbc, hcd, hda, hac, hbd,
      Ne.symm hab, Ne.symm hbc, Ne.symm hcd,
      Ne.symm hda, Ne.symm hac, Ne.symm hbd]
  by_contra hnone
  push_neg at hnone
  have hb1NotS : bad₁ ∉ S := by simpa only [S] using hnone.1
  have hb2NotS : bad₂ ∉ S := by simpa only [S] using hnone.2
  have hb1Comp : bad₁ ∈ (Finset.univ \ S : Finset W) :=
    Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hb1NotS⟩
  have hb2Comp : bad₂ ∈ (Finset.univ \ S : Finset W) :=
    Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hb2NotS⟩
  have hcompCard :
      (Finset.univ \ S : Finset W).card = 1 := by
    have hcardDiff :
        (Finset.univ \ S : Finset W).card =
          (Finset.univ : Finset W).card - S.card := by
      rw [Finset.card_sdiff]
      simp
    rw [hcardDiff, Finset.card_univ, hcard, hScard]
  have hEq :=
    Finset.card_eq_one.mp hcompCard
  obtain ⟨z, hz⟩ := hEq
  have hb1z : bad₁ = z := by
    have : bad₁ ∈ ({z} : Finset W) := by
      simpa [hz] using hb1Comp
    simpa using this
  have hb2z : bad₂ = z := by
    have : bad₂ ∈ ({z} : Finset W) := by
      simpa [hz] using hb2Comp
    simpa using this
  exact hbad (hb1z.trans hb2z.symm)

/-- A forced monochromatic C4 among the five minima contains at least one of
the two bad minima. -/
theorem monochromatic_fourCycle_contains_bad_minimum
    {V : Type*} [LinearOrder V] [Fintype V]
    {k : ℕ}
    (P : BinaryEdgePartition V k)
    (top bad₁ bad₂ : V)
    (htb₁ : top ≠ bad₁)
    (htb₂ : top ≠ bad₂)
    (hb₁₂ : bad₁ ≠ bad₂)
    (hcard : Fintype.card V = 6)
    (colour : Fin k)
    (hcycle : HasFourCycle (localColourGraph P top colour)) :
    let b₁ : OtherVertex top := ⟨bad₁, htb₁.symm⟩
    let b₂ : OtherVertex top := ⟨bad₂, htb₂.symm⟩
    ∃ a b c d : OtherVertex top,
      a ≠ b ∧ b ≠ c ∧ c ≠ d ∧ d ≠ a ∧
      a ≠ c ∧ b ≠ d ∧
      (localColourGraph P top colour).Adj a b ∧
      (localColourGraph P top colour).Adj b c ∧
      (localColourGraph P top colour).Adj c d ∧
      (localColourGraph P top colour).Adj d a ∧
      (b₁ ∈ ({a,b,c,d} : Finset (OtherVertex top)) ∨
       b₂ ∈ ({a,b,c,d} : Finset (OtherVertex top))) := by
  dsimp only
  obtain ⟨a,b,c,d,hab,hbc,hcd,hda,hac,hbd,
      habE,hbcE,hcdE,hdaE⟩ := hcycle
  have hcard5 :
      Fintype.card (OtherVertex top) = 5 :=
    card_otherVertex_eq_five_of_card_six hcard top
  have hb12' :
      (⟨bad₁, htb₁.symm⟩ : OtherVertex top) ≠
        ⟨bad₂, htb₂.symm⟩ := by
    intro h
    apply hb₁₂
    exact congrArg Subtype.val h
  have hmem :=
    one_of_two_distinct_vertices_mem_fourCycle_vertices
      hcard5 hb12' hab hbc hcd hda hac hbd
  exact ⟨a,b,c,d,hab,hbc,hcd,hda,hac,hbd,
    habE,hbcE,hcdE,hdaE,hmem⟩

/-- Main geometric incidence consequence: in the two-bad equality branch,
the forced monochromatic C4 supplies at least one saturation-bad minimum with
a strict sub-lambda cycle-neighbour angle. -/
theorem two_bad_monochromatic_fourCycle_gives_bad_small_angle
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane} (hp : Function.Injective p)
    {lam t delta c : ℝ}
    (hcap : AngleCap p lam)
    (C : ∀ v : V, CentreProjectiveCycle hp v) {n : ℕ}
    (hn4 : 4 ≤ n)
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
    (top bad₁ bad₂ : V)
    (htb₁ : top ≠ bad₁)
    (htb₂ : top ≠ bad₂)
    (hb₁₂ : bad₁ ≠ bad₂)
    (hcard : Fintype.card V = 6)
    (hTop :
      (active
        (uncoveredCutMergedPartition
          hp hcap C (by omega : 1 ≤ n)
          htpos hlam ht hdelta0 hdeltaHalf
          hc0 hcpi huncovered) top).card ≤ 1)
    (hBad₁ :
      (active
        (uncoveredCutMergedPartition
          hp hcap C (by omega : 1 ≤ n)
          htpos hlam ht hdelta0 hdeltaHalf
          hc0 hcpi huncovered) bad₁).card ≤ 4)
    (hBad₂ :
      (active
        (uncoveredCutMergedPartition
          hp hcap C (by omega : 1 ≤ n)
          htpos hlam ht hdelta0 hdeltaHalf
          hc0 hcpi huncovered) bad₂).card ≤ 4)
    (hOther :
      ∀ v : V,
        v ≠ top → v ≠ bad₁ → v ≠ bad₂ →
        (active
          (uncoveredCutMergedPartition
            hp hcap C (by omega : 1 ≤ n)
            htpos hlam ht hdelta0 hdeltaHalf
            hc0 hcpi huncovered) v).card ≤ 3)
    (hbadCut₁ :
      CutSaturationBadAt
        hp hcap C htpos hlam ht hdelta0
        (by linarith : delta < 1)
        hc0 hcpi bad₁)
    (hbadCut₂ :
      CutSaturationBadAt
        hp hcap C htpos hlam ht hdelta0
        (by linarith : delta < 1)
        hc0 hcpi bad₂) :
    ∃ bad x y : V,
      (bad = bad₁ ∨ bad = bad₂) ∧
      bad ≠ x ∧ bad ≠ y ∧ x ≠ y ∧
      EuclideanGeometry.angle (p x) (p bad) (p y) < lam := by
  let M :=
    uncoveredCutMergedPartition
      hp hcap C (by omega : 1 ≤ n)
      htpos hlam ht hdelta0 hdeltaHalf
      hc0 hcpi huncovered
  obtain ⟨root, colour, hcr, hcycle⟩ :=
    six_point_two_exception_has_monochromatic_fourCycle
      hn4 M top bad₁ bad₂
      htb₁ htb₂ hb₁₂ hcard
      hTop hBad₁ hBad₂ hOther
  obtain ⟨a,b,d,e,hab,hbd,hde,hea,had,hbe,
      habE,hbdE,hdeE,heaE,hmem⟩ :=
    monochromatic_fourCycle_contains_bad_minimum
      M top bad₁ bad₂ htb₁ htb₂ hb₁₂ hcard
      colour hcycle
  let B₁ : OtherVertex top := ⟨bad₁, htb₁.symm⟩
  let B₂ : OtherVertex top := ⟨bad₂, htb₂.symm⟩

  -- Normalize the four possible cycle corners once, rather than
  -- elaborating the heavy geometric lemma in eight duplicated branches.
  have hcorner (w : OtherVertex top)
      (hw : w ∈ ({a,b,d,e} : Finset (OtherVertex top))) :
      ∃ x y : OtherVertex top,
        w ≠ x ∧ w ≠ y ∧ x ≠ y ∧
        (localColourGraph M top colour).Adj w x ∧
        (localColourGraph M top colour).Adj y w := by
    simp only [Finset.mem_insert, Finset.mem_singleton] at hw
    rcases hw with h | h | h | h
    · subst w
      exact ⟨b,e,hab,hea.symm,hbe,habE,heaE⟩
    · subst w
      exact ⟨d,a,hbd,hab.symm,had.symm,hbdE,habE⟩
    · subst w
      exact ⟨e,b,hde,hbd.symm,hbe.symm,hdeE,hbdE⟩
    · subst w
      exact ⟨a,d,hea,hde.symm,had,heaE,hdeE⟩

  rcases hmem with hmem1 | hmem2
  · obtain ⟨x,y,hx,hy,hxy,hax,hya⟩ :=
      hcorner B₁ hmem1
    refine ⟨bad₁,x.1,y.1,Or.inl rfl, ?_, ?_, ?_, ?_⟩
    · exact fun h => hx (Subtype.ext h)
    · exact fun h => hy (Subtype.ext h)
    · exact fun h => hxy (Subtype.ext h)
    · simpa only [B₁] using
        (saturation_bad_vertex_of_monochromatic_fourCycle_has_small_angle
          hp hcap C (by omega : 1 ≤ n) htpos hlam ht hdelta0 hdeltaHalf
          hc0 hcpi huncovered top colour hx hy hxy
          hax hya hbadCut₁)
  · obtain ⟨x,y,hx,hy,hxy,hax,hya⟩ :=
      hcorner B₂ hmem2
    refine ⟨bad₂,x.1,y.1,Or.inr rfl, ?_, ?_, ?_, ?_⟩
    · exact fun h => hx (Subtype.ext h)
    · exact fun h => hy (Subtype.ext h)
    · exact fun h => hxy (Subtype.ext h)
    · simpa only [B₂] using
        (saturation_bad_vertex_of_monochromatic_fourCycle_has_small_angle
          hp hcap C (by omega : 1 ≤ n) htpos hlam ht hdelta0 hdeltaHalf
          hc0 hcpi huncovered top colour hx hy hxy
          hax hya hbadCut₂)

#print axioms one_of_two_distinct_vertices_mem_fourCycle_vertices
#print axioms monochromatic_fourCycle_contains_bad_minimum
#print axioms two_bad_monochromatic_fourCycle_gives_bad_small_angle

end JSP000404Research
