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
  have h0 : 2 ≤ (S 0).card := htwo (0 : Fin 3)
  have h1 : 2 ≤ (S 1).card := htwo (1 : Fin 3)
  have h2 : 2 ≤ (S 2).card := htwo (2 : Fin 3)
  rw [hunion] at hle
  omega

/-- STRONGER original-source six-centre obstruction: a genuine three-hit
opposite Boolean candidate forces at least SIX actual PROJECTED-LOSS
vertices, not merely six vertices in the ambient configuration.
Thus arbitrary numbers of non-loss centres do not weaken this bound. -/
theorem actual_three_colour_triple_fibre_forces_six_loss_centres
    {V : Type*} [LinearOrder V] [Fintype V]
    (C : OrderedEdgeColoring V (3 + 1))
    (exponent : V → ℕ)
    (choice : V → Fin 3)
    (hexp : ∀ v, exponent v ≤ 2)
    (q : Fin 3 → Bool)
    (hthree : 3 ≤ (actualLossOppositeCandidateFibre
      C exponent choice q).card) :
    6 ≤ (projectedLossVertices C exponent).card := by
  classical
  let S (c : Fin 3) := lossCoordinateSlice C exponent choice c
  have htwo := actual_three_colour_triple_fibre_each_slice_two_centres
    C exponent choice hexp q hthree
  have hdisj (c d : Fin 3) (hcd : c ≠ d) :
      Disjoint (S c) (S d) := by
    apply Finset.disjoint_left.mpr
    intro v hvc hvd
    have hcv := ((mem_lossCoordinateSlice C exponent choice c v).mp hvc).2
    have hdv := ((mem_lossCoordinateSlice C exponent choice d v).mp hvd).2
    exact hcd (hcv.symm.trans hdv)
  have h01 : Disjoint (S 0) (S 1) := hdisj 0 1 (by decide)
  have h02 : Disjoint (S 0) (S 2) := hdisj 0 2 (by decide)
  have h12 : Disjoint (S 1) (S 2) := hdisj 1 2 (by decide)
  have h012 : Disjoint (S 0 ∪ S 1) (S 2) :=
    Finset.disjoint_union_left.mpr ⟨h02, h12⟩
  have hcard :
      (S 0 ∪ S 1 ∪ S 2).card =
        (S 0).card + (S 1).card + (S 2).card := by
    rw [Finset.card_union_of_disjoint h012,
      Finset.card_union_of_disjoint h01]
  have hsource (c : Fin 3) :
      S c ⊆ projectedLossVertices C exponent := by
    intro v hv
    exact ((mem_lossCoordinateSlice C exponent choice c v).mp hv).1
  have hall :
      S 0 ∪ S 1 ∪ S 2 ⊆ projectedLossVertices C exponent := by
    intro v hv
    rcases Finset.mem_union.mp hv with hv01 | hv2
    · rcases Finset.mem_union.mp hv01 with hv0 | hv1
      · exact hsource 0 hv0
      · exact hsource 1 hv1
    · exact hsource 2 hv2
  have hle := Finset.card_le_card hall
  have h0 : 2 ≤ (S (0 : Fin 3)).card := htwo 0
  have h1 : 2 ≤ (S (1 : Fin 3)).card := htwo 1
  have h2 : 2 ≤ (S (2 : Fin 3)).card := htwo 2
  rw [hcard] at hle
  omega

#print axioms actual_three_colour_triple_fibre_forces_six_loss_centres

/-- Two distinct genuine n=3 opposite-candidate debt records require
at least FOUR distinct original projected-loss centres. The proof uses
the exact source pair signatures: distinct pair records share one choice
slice whose inverse source words disagree twice, so that slice needs two
distinct original owners; the other two slices each need one more. -/
theorem actual_three_colour_double_fibre_forces_four_loss_centres
    {V : Type*} [LinearOrder V] [Fintype V]
    (C : OrderedEdgeColoring V (3 + 1))
    (exponent : V → ℕ)
    (choice : V → Fin 3)
    (hexp : ∀ v, exponent v ≤ 2)
    (q : Fin 3 → Bool)
    (htwo : 2 ≤ (actualLossOppositeCandidateFibre
      C exponent choice q).card) :
    4 ≤ (projectedLossVertices C exponent).card := by
  classical
  let P := actualLossOppositeEligibleSourcePairs C exponent choice q
  have hcardP : 1 < P.card := by
    have h := actual_loss_opposite_candidate_fibre_card_eq_exact_source_pairs
      C exponent choice q
    dsimp only [P]
    omega
  have hPsub : P ⊆ actualLossOrderedCoordinatePairs 3 := by
    intro x hx
    exact (Finset.mem_filter.mp hx).1
  have hlegal : actualLossOrderedCoordinatePairs 3 =
      ({((1 : Fin 3), (0 : Fin 3)),
        ((2 : Fin 3), (0 : Fin 3)),
        ((2 : Fin 3), (1 : Fin 3))} : Finset (Fin 3 × Fin 3)) := by
    decide
  obtain ⟨x,hx,y,hy,hxy⟩ := Finset.one_lt_card.mp hcardP
  have hxCases : x = ((1 : Fin 3), (0 : Fin 3)) ∨
      x = ((2 : Fin 3), (0 : Fin 3)) ∨
      x = ((2 : Fin 3), (1 : Fin 3)) := by
    have h := hPsub hx
    rw [hlegal] at h
    simpa only [Finset.mem_insert, Finset.mem_singleton] using h
  have hyCases : y = ((1 : Fin 3), (0 : Fin 3)) ∨
      y = ((2 : Fin 3), (0 : Fin 3)) ∨
      y = ((2 : Fin 3), (1 : Fin 3)) := by
    have h := hPsub hy
    rw [hlegal] at h
    simpa only [Finset.mem_insert, Finset.mem_singleton] using h
  have hpair :
      (((1 : Fin 3), (0 : Fin 3)) ∈ P ∧
        ((2 : Fin 3), (0 : Fin 3)) ∈ P) ∨
      (((1 : Fin 3), (0 : Fin 3)) ∈ P ∧
        ((2 : Fin 3), (1 : Fin 3)) ∈ P) ∨
      (((2 : Fin 3), (0 : Fin 3)) ∈ P ∧
        ((2 : Fin 3), (1 : Fin 3)) ∈ P) := by
    rcases hxCases with rfl | rfl | rfl <;>
      rcases hyCases with rfl | rfl | rfl
    · exact (hxy rfl).elim
    · exact Or.inl ⟨hx,hy⟩
    · exact Or.inr (Or.inl ⟨hx,hy⟩)
    · exact Or.inl ⟨hy,hx⟩
    · exact (hxy rfl).elim
    · exact Or.inr (Or.inr ⟨hx,hy⟩)
    · exact Or.inr (Or.inl ⟨hy,hx⟩)
    · exact Or.inr (Or.inr ⟨hy,hx⟩)
    · exact (hxy rfl).elim
  let w10 := flipBoolWordAt (flipBoolWordAt q (0 : Fin 3)) (1 : Fin 3)
  let w20 := flipBoolWordAt (flipBoolWordAt q (0 : Fin 3)) (2 : Fin 3)
  let w21 := flipBoolWordAt (flipBoolWordAt q (1 : Fin 3)) (2 : Fin 3)
  obtain ⟨hd10_20_1,hd10_20_2,hd10_21_0,hd10_21_2,
    hd20_21_0,hd20_21_1⟩ :=
      three_corner_source_disagreement_pattern q
  have hFour (c d e : Fin 3) (hcd : c ≠ d) (hce : c ≠ e)
      (hde : d ≠ e) (w z : Fin 3 → Bool)
      (hwd : w d ≠ z d) (hwe : w e ≠ z e)
      (hwc : w ∈ translatedLossSliceWords C exponent choice c)
      (hzc : z ∈ translatedLossSliceWords C exponent choice c)
      (hwOther : w ∈ translatedLossSliceWords C exponent choice d)
      (hzOther : z ∈ translatedLossSliceWords C exponent choice e) :
      4 ≤ (projectedLossVertices C exponent).card := by
    let S (i : Fin 3) := lossCoordinateSlice C exponent choice i
    obtain ⟨v,hvc,u,huc,hvu⟩ :=
      translated_slice_two_disagreements_two_distinct_owners
        C exponent choice hexp c d e hde w z hwd hwe hwc hzc
    have htwoC : 2 ≤ (S c).card := by
      have hsub : ({v,u} : Finset V) ⊆ S c := by
        intro z hz
        simp only [Finset.mem_insert, Finset.mem_singleton] at hz
        rcases hz with rfl | rfl
        · exact hvc
        · exact huc
      have h := Finset.card_le_card hsub
      have hcard : ({v,u} : Finset V).card = 2 := by simp [hvu]
      omega
    obtain ⟨vd,hvd,_⟩ := Finset.mem_biUnion.mp hwOther
    obtain ⟨ve,hve,_⟩ := Finset.mem_biUnion.mp hzOther
    have honeD : 1 ≤ (S d).card := Finset.one_le_card.mpr ⟨vd,hvd⟩
    have honeE : 1 ≤ (S e).card := Finset.one_le_card.mpr ⟨ve,hve⟩
    have hdisj (a b : Fin 3) (hab : a ≠ b) : Disjoint (S a) (S b) := by
      apply Finset.disjoint_left.mpr
      intro v hav hbv
      have hca := ((mem_lossCoordinateSlice C exponent choice a v).mp hav).2
      have hcb := ((mem_lossCoordinateSlice C exponent choice b v).mp hbv).2
      exact hab (hca.symm.trans hcb)
    have hdcd : Disjoint (S c) (S d) := hdisj c d hcd
    have hdce : Disjoint (S c) (S e) := hdisj c e hce
    have hdde : Disjoint (S d) (S e) := hdisj d e hde
    have hwhole : Disjoint (S c ∪ S d) (S e) :=
      Finset.disjoint_union_left.mpr ⟨hdce,hdde⟩
    have hcount :
        (S c ∪ S d ∪ S e).card =
          (S c).card + (S d).card + (S e).card := by
      rw [Finset.card_union_of_disjoint hwhole,
        Finset.card_union_of_disjoint hdcd]
    have hsrc (i : Fin 3) :
        S i ⊆ projectedLossVertices C exponent := by
      intro v hv
      exact ((mem_lossCoordinateSlice C exponent choice i v).mp hv).1
    have hsub :
        S c ∪ S d ∪ S e ⊆ projectedLossVertices C exponent := by
      intro v hv
      rcases Finset.mem_union.mp hv with hv12 | hve
      · rcases Finset.mem_union.mp hv12 with hvc' | hvd'
        · exact hsrc c hvc'
        · exact hsrc d hvd'
      · exact hsrc e hve
    have hbound := Finset.card_le_card hsub
    rw [hcount] at hbound
    omega
  rcases hpair with ⟨h10P,h20P⟩ | ⟨h10P,h21P⟩ | ⟨h20P,h21P⟩
  · have h10 := (Finset.mem_filter.mp h10P).2
    have h20 := (Finset.mem_filter.mp h20P).2
    have h10p := Finset.mem_inter.mp (Finset.mem_sdiff.mp h10).1
    have h20p := Finset.mem_inter.mp (Finset.mem_sdiff.mp h20).1
    have hw10_0 : w10 ∈ translatedLossSliceWords C exponent choice 0 := by
      simpa [w10,lossSliceAtNat] using h10p.2
    have hw10_1 : w10 ∈ translatedLossSliceWords C exponent choice 1 := by
      simpa [w10,lossSliceAtNat] using h10p.1
    have hw20_0 : w20 ∈ translatedLossSliceWords C exponent choice 0 := by
      simpa [w20,lossSliceAtNat] using h20p.2
    have hw20_2 : w20 ∈ translatedLossSliceWords C exponent choice 2 := by
      simpa [w20,lossSliceAtNat] using h20p.1
    exact hFour 0 1 2 (by decide) (by decide) (by decide)
      w10 w20 hd10_20_1 hd10_20_2 hw10_0 hw20_0 hw10_1 hw20_2
  · have h10 := (Finset.mem_filter.mp h10P).2
    have h21 := (Finset.mem_filter.mp h21P).2
    have h10p := Finset.mem_inter.mp (Finset.mem_sdiff.mp h10).1
    have h21p := Finset.mem_inter.mp (Finset.mem_sdiff.mp h21).1
    have hw10_1 : w10 ∈ translatedLossSliceWords C exponent choice 1 := by
      simpa [w10,lossSliceAtNat] using h10p.1
    have hw10_0 : w10 ∈ translatedLossSliceWords C exponent choice 0 := by
      simpa [w10,lossSliceAtNat] using h10p.2
    have hw21_1 : w21 ∈ translatedLossSliceWords C exponent choice 1 := by
      simpa [w21,lossSliceAtNat] using h21p.2
    have hw21_2 : w21 ∈ translatedLossSliceWords C exponent choice 2 := by
      simpa [w21,lossSliceAtNat] using h21p.1
    exact hFour 1 0 2 (by decide) (by decide) (by decide)
      w10 w21 hd10_21_0 hd10_21_2 hw10_1 hw21_1 hw10_0 hw21_2
  · have h20 := (Finset.mem_filter.mp h20P).2
    have h21 := (Finset.mem_filter.mp h21P).2
    have h20p := Finset.mem_inter.mp (Finset.mem_sdiff.mp h20).1
    have h21p := Finset.mem_inter.mp (Finset.mem_sdiff.mp h21).1
    have hw20_2 : w20 ∈ translatedLossSliceWords C exponent choice 2 := by
      simpa [w20,lossSliceAtNat] using h20p.1
    have hw20_0 : w20 ∈ translatedLossSliceWords C exponent choice 0 := by
      simpa [w20,lossSliceAtNat] using h20p.2
    have hw21_2 : w21 ∈ translatedLossSliceWords C exponent choice 2 := by
      simpa [w21,lossSliceAtNat] using h21p.1
    have hw21_1 : w21 ∈ translatedLossSliceWords C exponent choice 1 := by
      simpa [w21,lossSliceAtNat] using h21p.2
    exact hFour 2 0 1 (by decide) (by decide) (by decide)
      w20 w21 hd20_21_0 hd20_21_1 hw20_2 hw21_2 hw20_0 hw21_1

#print axioms actual_three_colour_double_fibre_forces_four_loss_centres

/-- At most THREE genuine projected-loss centres imply NO repeat of
any canonical earliest-prior opposite-candidate source target. This
holds independent of all other ambient centres and does not assume
exterior-hole eligibility. -/
theorem actual_three_colour_three_loss_centre_no_double_fibre
    {V : Type*} [LinearOrder V] [Fintype V]
    (C : OrderedEdgeColoring V (3 + 1))
    (exponent : V → ℕ) (choice : V → Fin 3)
    (hexp : ∀ v, exponent v ≤ 2)
    (hloss : (projectedLossVertices C exponent).card ≤ 3)
    (q : Fin 3 → Bool) :
    (actualLossOppositeCandidateFibre C exponent choice q).card ≤ 1 := by
  by_contra hnot
  have htwo : 2 ≤ (actualLossOppositeCandidateFibre
      C exponent choice q).card := by omega
  have hfour := actual_three_colour_double_fibre_forces_four_loss_centres
    C exponent choice hexp q htwo
  omega

#print axioms actual_three_colour_three_loss_centre_no_double_fibre

#print axioms translated_cube_two_words_agree_at_retained_active
#print axioms translated_cube_two_disagreements_impossible
#print axioms three_colour_projected_loss_two_active
#print axioms translated_slice_two_disagreements_two_distinct_owners
#print axioms three_corner_source_disagreement_pattern
#print axioms actual_three_colour_triple_fibre_each_slice_two_centres
#print axioms actual_three_colour_triple_fibre_forces_six_centres

end OrderedEdgeColoring
end JSP000404Research
