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

theorem one_of_two_distinct_vertices_mem_fourCycle_vertices
    {W : Type*} [Fintype W]
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
  have hb1Comp : bad₁ ∈ (Finset.univ  S : Finset W) := by
    simp [hnone.1]
  have hb2Comp : bad₂ ∈ (Finset.univ  S : Finset W) := by
    simp [hnone.2]
  have hcompCard :
      (Finset.univ  S : Finset W).card = 1 := by
    rw [Finset.card_sdiff]
    · rw [Finset.card_univ, hcard, hScard]
      omega
    · exact Finset.subset_univ S
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
    (hcap : AngleCap p lam)
    (C : ∀ v : V, CentreProjectiveCycle hp v)
    {lam t delta c : ℝ} {n : ℕ}
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
  rcases hmem with hmem1 | hmem2
  · simp only [Finset.mem_insert, Finset.mem_singleton] at hmem1
    rcases hmem1 with h1 | h1 | h1 | h1
    · subst a
      refine ⟨bad₁,b.1,e.1,Or.inl rfl, ?_, ?_, ?_, ?_⟩
      · exact fun h => hab (Subtype.ext h.symm)
      · exact fun h => hea (Subtype.ext h)
      · exact fun h => hbe (Subtype.ext h)
      · exact saturation_bad_vertex_of_monochromatic_fourCycle_has_small_angle
          hp hcap C (by omega : 1 ≤ n) htpos hlam ht hdelta0 hdeltaHalf
          hc0 hcpi huncovered top colour hab hea hbe
          habE heaE hbadCut₁
    · subst b
      refine ⟨bad₁,a.1,d.1,Or.inl rfl, ?_, ?_, ?_, ?_⟩
      · exact fun h => hab (Subtype.ext h)
      · exact fun h => hbd (Subtype.ext h.symm)
      · exact fun h => had (Subtype.ext h)
      · exact saturation_bad_vertex_of_monochromatic_fourCycle_has_small_angle
          hp hcap C (by omega : 1 ≤ n) htpos hlam ht hdelta0 hdeltaHalf
          hc0 hcpi huncovered top colour hab hbd had
          habE.symm hbdE hbadCut₁
    · subst d
      refine ⟨bad₁,b.1,e.1,Or.inl rfl, ?_, ?_, ?_, ?_⟩
      · exact fun h => hbd (Subtype.ext h)
      · exact fun h => hde (Subtype.ext h.symm)
      · exact fun h => hbe (Subtype.ext h)
      · exact saturation_bad_vertex_of_monochromatic_fourCycle_has_small_angle
          hp hcap C (by omega : 1 ≤ n) htpos hlam ht hdelta0 hdeltaHalf
          hc0 hcpi huncovered top colour hbd hde hbe
          hbdE.symm hdeE hbadCut₁
    · subst e
      refine ⟨bad₁,d.1,a.1,Or.inl rfl, ?_, ?_, ?_, ?_⟩
      · exact fun h => hde (Subtype.ext h)
      · exact fun h => hea (Subtype.ext h.symm)
      · exact fun h => had (Subtype.ext h.symm)
      · exact saturation_bad_vertex_of_monochromatic_fourCycle_has_small_angle
          hp hcap C (by omega : 1 ≤ n) htpos hlam ht hdelta0 hdeltaHalf
          hc0 hcpi huncovered top colour hde hea had
          hdeE.symm heaE hbadCut₁
  · simp only [Finset.mem_insert, Finset.mem_singleton] at hmem2
    rcases hmem2 with h2 | h2 | h2 | h2
    · subst a
      refine ⟨bad₂,b.1,e.1,Or.inr rfl, ?_, ?_, ?_, ?_⟩
      · exact fun h => hab (Subtype.ext h.symm)
      · exact fun h => hea (Subtype.ext h)
      · exact fun h => hbe (Subtype.ext h)
      · exact saturation_bad_vertex_of_monochromatic_fourCycle_has_small_angle
          hp hcap C (by omega : 1 ≤ n) htpos hlam ht hdelta0 hdeltaHalf
          hc0 hcpi huncovered top colour hab hea hbe
          habE heaE hbadCut₂
    · subst b
      refine ⟨bad₂,a.1,d.1,Or.inr rfl, ?_, ?_, ?_, ?_⟩
      · exact fun h => hab (Subtype.ext h)
      · exact fun h => hbd (Subtype.ext h.symm)
      · exact fun h => had (Subtype.ext h)
      · exact saturation_bad_vertex_of_monochromatic_fourCycle_has_small_angle
          hp hcap C (by omega : 1 ≤ n) htpos hlam ht hdelta0 hdeltaHalf
          hc0 hcpi huncovered top colour hab hbd had
          habE.symm hbdE hbadCut₂
    · subst d
      refine ⟨bad₂,b.1,e.1,Or.inr rfl, ?_, ?_, ?_, ?_⟩
      · exact fun h => hbd (Subtype.ext h)
      · exact fun h => hde (Subtype.ext h.symm)
      · exact fun h => hbe (Subtype.ext h)
      · exact saturation_bad_vertex_of_monochromatic_fourCycle_has_small_angle
          hp hcap C (by omega : 1 ≤ n) htpos hlam ht hdelta0 hdeltaHalf
          hc0 hcpi huncovered top colour hbd hde hbe
          hbdE.symm hdeE hbadCut₂
    · subst e
      refine ⟨bad₂,d.1,a.1,Or.inr rfl, ?_, ?_, ?_, ?_⟩
      · exact fun h => hde (Subtype.ext h)
      · exact fun h => hea (Subtype.ext h.symm)
      · exact fun h => had (Subtype.ext h.symm)
      · exact saturation_bad_vertex_of_monochromatic_fourCycle_has_small_angle
          hp hcap C (by omega : 1 ≤ n) htpos hlam ht hdelta0 hdeltaHalf
          hc0 hcpi huncovered top colour hde hea had
          hdeE.symm heaE hbadCut₂

#print axioms one_of_two_distinct_vertices_mem_fourCycle_vertices
#print axioms monochromatic_fourCycle_contains_bad_minimum
#print axioms two_bad_monochromatic_fourCycle_gives_bad_small_angle

end JSP000404Research
