import JSP000404Research.ResidualLossTripleFibreGlobalPaymentBarrier
import JSP000404Research.ResidualLossCoordinateSlices
import JSP000404Research.TranslatedCompletionCore
import JSP000404Research.ResidualProjectionLoss
import Mathlib.Tactic

/-!
# Six genuinely distinct projected-loss centres forced by an n=3 triple fibre

For exponent(v)<=2 in n=3, each actual projected-loss source retains at
least TWO active Boolean coordinates. Its translated completion cube
therefore cannot contain two words disagreeing at TWO distinct positions.
A genuine 3-source opposite-candidate fibre forces in EACH of the three
choice-coordinate slices two source words differing at exactly two
Boolean positions. Hence EACH such slice must contain >=2 DISTINCT
original projected-loss centres. Distinct choice slices are vertex
disjoint, forcing SIX actual centres, not fictitious token owners.

This is an actual geometric-structural exclusion of triple fibres in
ALL five-centre n=3 profiles satisfying the genuine exponent bound.
It does NOT pay the other original debt types or settle JSP-000404.
-/

namespace JSP000404Research
namespace OrderedEdgeColoring

/-- Original completion cubes impose equal bits at all actual active
coordinates, even after both Boolean words receive the SAME flip. -/
theorem translated_cube_two_words_agree_at_retained_active
    {V : Type*} [LinearOrder V]
    (C : OrderedEdgeColoring V (3 + 1))
    (v : V) (c : Fin 3)
    (w z : Fin 3 → Bool)
    (hw : w ∈ translatedCompletionWords C v c)
    (hz : z ∈ translatedCompletionWords C v c)
    (d : Fin 3) (hd : d ∈ retainedActive C v) :
    w d = z d := by
  have hwr := (mem_translatedCompletionWords C v c w).mp hw
  have hzr := (mem_translatedCompletionWords C v c z).mp hz
  have hwd := (mem_retainedCompletionWords C v (flipBoolWordAt w c)).mp hwr d hd
  have hzd := (mem_retainedCompletionWords C v (flipBoolWordAt z c)).mp hzr d hd
  have hsame : flipBoolWordAt w c d = flipBoolWordAt z c d :=
    hwd.trans hzd.symm
  by_cases hdc : d = c
  · subst d
    rw [flipBoolWordAt_at, flipBoolWordAt_at] at hsame
    cases hwc : w c <;> cases hzc : z c <;>
      simp [hwc, hzc] at hsame ⊢
  · simpa only [flipBoolWordAt_off w hdc,
      flipBoolWordAt_off z hdc] using hsame

/-- An n=3 Boolean subcube with at least two retained active positions
cannot contain two words differing at two distinct coordinates. -/
theorem translated_cube_two_disagreements_impossible
    {V : Type*} [LinearOrder V]
    (C : OrderedEdgeColoring V (3 + 1))
    (v : V) (c : Fin 3)
    (w z : Fin 3 → Bool)
    (d e : Fin 3) (hde : d ≠ e)
    (hdiff : w d ≠ z d) (hediff : w e ≠ z e)
    (hactive : 2 ≤ (retainedActive C v).card) :
    ¬ (w ∈ translatedCompletionWords C v c ∧
        z ∈ translatedCompletionWords C v c) := by
  classical
  rintro ⟨hw,hz⟩
  have hnotd : d ∉ retainedActive C v := by
    intro hd
    exact hdiff (translated_cube_two_words_agree_at_retained_active
      C v c w z hw hz d hd)
  have hnote : e ∉ retainedActive C v := by
    intro he
    exact hediff (translated_cube_two_words_agree_at_retained_active
      C v c w z hw hz e he)
  have hsub :
      retainedActive C v ⊆
        ((Finset.univ : Finset (Fin 3)) \
          ({d,e} : Finset (Fin 3))) := by
    intro x hx
    apply Finset.mem_sdiff.mpr
    constructor
    · exact Finset.mem_univ _
    · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      constructor
      · intro heq
        subst x
        exact hnotd hx
      · intro heq
        subst x
        exact hnote hx
  have hrest :
      ∀ (a b : Fin 3), a ≠ b →
        ((Finset.univ : Finset (Fin 3)) \
          ({a,b} : Finset (Fin 3))).card = 1 := by
    decide
  have hc := Finset.card_le_card hsub
  rw [hrest d e hde] at hc
  omega

/-- Every ACTUAL projected-loss vertex under exponent<=2 in
n=3 has at least two retained active Boolean coordinates. -/
theorem three_colour_projected_loss_two_active
    {V : Type*} [LinearOrder V] [Fintype V]
    (C : OrderedEdgeColoring V (3 + 1))
    (exponent : V → ℕ)
    (hexp : ∀ v, exponent v ≤ 2)
    (v : V) (hv : v ∈ projectedLossVertices C exponent) :
    2 ≤ (retainedActive C v).card := by
  have hrigid :=
    (mem_projectedLossVertices C exponent v).mp hv
  have hcard : (retainedActive C v).card ≤ 3 :=
    Finset.card_le_univ (retainedActive C v)
  have hvbound := hexp v
  unfold projectedFree at hrigid
  omega

/-- Two ACTUAL translated-loss words differing in two Boolean
coordinates require two DIFFERENT original projected-loss source
centres in their common choice-coordinate slice. -/
theorem translated_slice_two_disagreements_two_distinct_owners
    {V : Type*} [LinearOrder V] [Fintype V]
    (C : OrderedEdgeColoring V (3 + 1))
    (exponent : V → ℕ)
    (choice : V → Fin 3)
    (hexp : ∀ v, exponent v ≤ 2)
    (c d e : Fin 3) (hde : d ≠ e)
    (w z : Fin 3 → Bool)
    (hdiff : w d ≠ z d) (hediff : w e ≠ z e)
    (hw : w ∈ translatedLossSliceWords C exponent choice c)
    (hz : z ∈ translatedLossSliceWords C exponent choice c) :
    ∃ v ∈ lossCoordinateSlice C exponent choice c,
      ∃ u ∈ lossCoordinateSlice C exponent choice c, v ≠ u := by
  classical
  obtain ⟨v,hv,hvw⟩ := Finset.mem_biUnion.mp hw
  obtain ⟨u,hu,huz⟩ := Finset.mem_biUnion.mp hz
  have hproj : v ∈ projectedLossVertices C exponent :=
    ((mem_lossCoordinateSlice C exponent choice c v).mp hv).1
  have hactive := three_colour_projected_loss_two_active C exponent hexp v hproj
  refine ⟨v,hv,u,hu,?_⟩
  intro heq
  subst u
  exact translated_cube_two_disagreements_impossible
    C v c w z d e hde hdiff hediff hactive ⟨hvw,huz⟩

/-- The THREE actual inverse source-word pairs have the two-bit
disagreement pattern: pair 10 versus 20 changes 1,2; pair 10
versus 21 changes 0,2; pair 20 versus 21 changes 0,1. -/
theorem three_corner_source_disagreement_pattern :
    ∀ q : Fin 3 → Bool,
      let w10 := flipBoolWordAt (flipBoolWordAt q (0 : Fin 3)) (1 : Fin 3)
      let w20 := flipBoolWordAt (flipBoolWordAt q (0 : Fin 3)) (2 : Fin 3)
      let w21 := flipBoolWordAt (flipBoolWordAt q (1 : Fin 3)) (2 : Fin 3)
      (w10 (1 : Fin 3) ≠ w20 (1 : Fin 3)) ∧
      (w10 (2 : Fin 3) ≠ w20 (2 : Fin 3)) ∧
      (w10 (0 : Fin 3) ≠ w21 (0 : Fin 3)) ∧
      (w10 (2 : Fin 3) ≠ w21 (2 : Fin 3)) ∧
      (w20 (0 : Fin 3) ≠ w21 (0 : Fin 3)) ∧
      (w20 (1 : Fin 3) ≠ w21 (1 : Fin 3)) := by
  decide

/-- Each of the three ACTUAL chosen-coordinate projected-loss source
slices has at least TWO DIFFERENT actual vertices when the original
n=3 opposite fibre has cardinal three. -/
theorem actual_three_colour_triple_fibre_each_slice_two_centres
    {V : Type*} [LinearOrder V] [Fintype V]
    (C : OrderedEdgeColoring V (3 + 1))
    (exponent : V → ℕ)
    (choice : V → Fin 3)
    (hexp : ∀ v, exponent v ≤ 2)
    (q : Fin 3 → Bool)
    (hthree : 3 ≤ (actualLossOppositeCandidateFibre
      C exponent choice q).card) :
    ∀ c : Fin 3, 2 ≤ (lossCoordinateSlice C exponent choice c).card := by
  classical
  rcases actual_three_colour_triple_fibre_all_source_tests
    C exponent choice q hthree with ⟨h10,h20,h21⟩
  let w10 := flipBoolWordAt (flipBoolWordAt q (0 : Fin 3)) (1 : Fin 3)
  let w20 := flipBoolWordAt (flipBoolWordAt q (0 : Fin 3)) (2 : Fin 3)
  let w21 := flipBoolWordAt (flipBoolWordAt q (1 : Fin 3)) (2 : Fin 3)
  obtain ⟨hd10_20_1,hd10_20_2,hd10_21_0,hd10_21_2,
    hd20_21_0,hd20_21_1⟩ :=
      three_corner_source_disagreement_pattern q
  have h10p := (Finset.mem_inter.mp (Finset.mem_sdiff.mp h10).1)
  have h20p := (Finset.mem_inter.mp (Finset.mem_sdiff.mp h20).1)
  have h21p := (Finset.mem_inter.mp (Finset.mem_sdiff.mp h21).1)
  have hw10_0 : w10 ∈ translatedLossSliceWords C exponent choice (0 : Fin 3) := by
    simpa [w10,lossSliceAtNat] using h10p.2
  have hw10_1 : w10 ∈ translatedLossSliceWords C exponent choice (1 : Fin 3) := by
    simpa [w10,lossSliceAtNat] using h10p.1
  have hw20_0 : w20 ∈ translatedLossSliceWords C exponent choice (0 : Fin 3) := by
    simpa [w20,lossSliceAtNat] using h20p.2
  have hw20_2 : w20 ∈ translatedLossSliceWords C exponent choice (2 : Fin 3) := by
    simpa [w20,lossSliceAtNat] using h20p.1
  have hw21_1 : w21 ∈ translatedLossSliceWords C exponent choice (1 : Fin 3) := by
    simpa [w21,lossSliceAtNat] using h21p.2
  have hw21_2 : w21 ∈ translatedLossSliceWords C exponent choice (2 : Fin 3) := by
    simpa [w21,lossSliceAtNat] using h21p.1
  have htwo (c : Fin 3) (d e : Fin 3) (hde : d ≠ e)
      (w z : Fin 3 → Bool) (hwd : w d ≠ z d) (hwe : w e ≠ z e)
      (hw : w ∈ translatedLossSliceWords C exponent choice c)
      (hz : z ∈ translatedLossSliceWords C exponent choice c) :
      2 ≤ (lossCoordinateSlice C exponent choice c).card := by
    obtain ⟨v,hv,u,hu,hvu⟩ :=
      translated_slice_two_disagreements_two_distinct_owners
        C exponent choice hexp c d e hde w z hwd hwe hw hz
    have hsub : ({v,u} : Finset V) ⊆
        lossCoordinateSlice C exponent choice c := by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl
      · exact hv
      · exact hu
    have hh := Finset.card_le_card hsub
    have htwoCard : ({v,u} : Finset V).card = 2 := by
      simp [hvu]
    omega
  intro c
  fin_cases c
  · exact htwo 0 1 2 (by decide) w10 w20 hd10_20_1 hd10_20_2 hw10_0 hw20_0
  · exact htwo 1 0 2 (by decide) w10 w21 hd10_21_0 hd10_21_2 hw10_1 hw21_1
  · exact htwo 2 0 1 (by decide) w20 w21 hd20_21_0 hd20_21_1 hw20_2 hw21_2

/-- A genuine three-collision fibre in n=3 requires AT LEAST SIX
original centres, each an actual projected-loss vertex, with two
vertices for EACH mutually disjoint choice coordinate.  Thus a
five-centre configuration CANNOT exhibit this obstruction. -/
theorem actual_three_colour_triple_fibre_forces_six_centres
    {V : Type*} [LinearOrder V] [Fintype V]
    (C : OrderedEdgeColoring V (3 + 1))
    (exponent : V → ℕ)
    (choice : V → Fin 3)
    (hexp : ∀ v, exponent v ≤ 2)
    (q : Fin 3 → Bool)
    (hthree : 3 ≤ (actualLossOppositeCandidateFibre
      C exponent choice q).card) :
    6 ≤ Fintype.card V := by
  classical
  let S (c : Fin 3) := lossCoordinateSlice C exponent choice c
  have htwo := actual_three_colour_triple_fibre_each_slice_two_centres
    C exponent choice hexp q hthree
  have hdisj (c d : Fin 3) (hcd : c ≠ d) : Disjoint (S c) (S d) := by
    apply Finset.disjoint_left.mpr
    intro v hvc hvd
    have hcv := ((mem_lossCoordinateSlice C exponent choice c v).mp hvc).2
    have hdv := ((mem_lossCoordinateSlice C exponent choice d v).mp hvd).2
    exact hcd (hcv.symm.trans hdv)
  have h01 : Disjoint (S 0) (S 1) := hdisj 0 1 (by decide)
  have h02 : Disjoint (S 0) (S 2) := hdisj 0 2 (by decide)
  have h12 : Disjoint (S 1) (S 2) := hdisj 1 2 (by decide)
  have h012 : Disjoint (S 0 ∪ S 1) (S 2) := by
    exact Finset.disjoint_union_left.mpr ⟨h02,h12⟩
  have hunion :
      (S 0 ∪ S 1 ∪ S 2).card =
        (S 0).card + (S 1).card + (S 2).card := by
    rw [Finset.card_union_of_disjoint h012,
      Finset.card_union_of_disjoint h01]
  have hle : (S 0 ∪ S 1 ∪ S 2).card ≤ Fintype.card V := by
    have hsub : S 0 ∪ S 1 ∪ S 2 ⊆ (Finset.univ : Finset V) := by
      intro v _; exact Finset.mem_univ _
    simpa only [Finset.card_univ] using Finset.card_le_card hsub
  have h0 := htwo (0 : Fin 3)
  have h1 := htwo (1 : Fin 3)
  have h2 := htwo (2 : Fin 3)
  omega

#print axioms translated_cube_two_words_agree_at_retained_active
#print axioms translated_cube_two_disagreements_impossible
#print axioms three_colour_projected_loss_two_active
#print axioms translated_slice_two_disagreements_two_distinct_owners
#print axioms three_corner_source_disagreement_pattern
#print axioms actual_three_colour_triple_fibre_each_slice_two_centres
#print axioms actual_three_colour_triple_fibre_forces_six_centres

end OrderedEdgeColoring
end JSP000404Research
