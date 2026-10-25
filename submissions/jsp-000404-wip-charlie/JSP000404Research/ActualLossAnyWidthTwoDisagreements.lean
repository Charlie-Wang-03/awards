import JSP000404Research.ActualTwoLossCentreNoReuse
import Mathlib.Tactic

/-!
# Genuine source-cube two-bit rigidity at arbitrary retained width

This isolates the dimension-free key behind the n=3 four-loss-centre
double-collision obstruction: under the original exponent <= 2 restriction,
a TRUE projected-loss centre retains all but at most one Boolean coordinate.
Consequently two translated source words disagreeing at two distinct
coordinates must come from DIFFERENT original loss owners.

This is a certified geometric/combinatorial dependency, not an assumption
of exterior holes, global source matching, or dyadic surplus.
-/

namespace JSP000404Research
namespace OrderedEdgeColoring

/-- The actual one-layer projected-loss equation and exponent <=2 imply
that all but at most ONE retained coordinate is active, for arbitrary n. -/
theorem any_width_projected_loss_retains_all_but_one
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexp : ∀ v, exponent v ≤ 2)
    (v : V) (hv : v ∈ projectedLossVertices C exponent) :
    n ≤ (retainedActive C v).card + 1 := by
  have hrigid := (mem_projectedLossVertices C exponent v).mp hv
  have hcard : (retainedActive C v).card ≤ n :=
    Finset.card_le_univ (retainedActive C v)
  have hvbound := hexp v
  unfold projectedFree at hrigid
  omega

/-- Two words in a SINGLE actual translated completion cube agree at
every retained-active coordinate. This is independent of Boolean width. -/
theorem any_width_translated_cube_agrees_at_retained_active
    {V : Type*} [LinearOrder V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (v : V) (c : Fin n)
    (w z : Fin n → Bool)
    (hw : w ∈ translatedCompletionWords C v c)
    (hz : z ∈ translatedCompletionWords C v c)
    (d : Fin n) (hd : d ∈ retainedActive C v) :
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

/-- A translated cube with n-1 or more retained-active coordinates
CANNOT contain two Boolean words disagreeing in two distinct positions. -/
theorem any_width_translated_cube_two_disagreements_impossible
    {V : Type*} [LinearOrder V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (v : V) (c : Fin n)
    (w z : Fin n → Bool)
    (d e : Fin n) (hde : d ≠ e)
    (hdiff : w d ≠ z d) (hediff : w e ≠ z e)
    (hactive : n ≤ (retainedActive C v).card + 1) :
    ¬ (w ∈ translatedCompletionWords C v c ∧
        z ∈ translatedCompletionWords C v c) := by
  classical
  rintro ⟨hw,hz⟩
  have hnotd : d ∉ retainedActive C v := by
    intro hd
    exact hdiff (any_width_translated_cube_agrees_at_retained_active
      C v c w z hw hz d hd)
  have hnote : e ∉ retainedActive C v := by
    intro he
    exact hediff (any_width_translated_cube_agrees_at_retained_active
      C v c w z hw hz e he)
  have hsub :
      retainedActive C v ⊆
        ((Finset.univ : Finset (Fin n)) \
          ({d,e} : Finset (Fin n))) := by
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
  have hpartition := Finset.card_sdiff_add_card_inter
    (Finset.univ : Finset (Fin n)) ({d,e} : Finset (Fin n))
  have hrest :
      (((Finset.univ : Finset (Fin n)) \
        ({d,e} : Finset (Fin n))).card) + 2 = n := by
    simpa [hde] using hpartition
  have hbound := Finset.card_le_card hsub
  omega

/-- Distinct true source words disagreeing at two coordinates in one
fixed original chosen-coordinate loss slice require two distinct
ACTUAL original projected-loss owners. Neither source is fabricated. -/
theorem any_width_translated_slice_two_disagreements_distinct_owners
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ) (choice : V → Fin n)
    (hexp : ∀ v, exponent v ≤ 2)
    (c d e : Fin n) (hde : d ≠ e)
    (w z : Fin n → Bool)
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
  have hactive :=
    any_width_projected_loss_retains_all_but_one
      C exponent hexp v hproj
  refine ⟨v,hv,u,hu,?_⟩
  intro heq
  subst u
  exact any_width_translated_cube_two_disagreements_impossible
    C v c w z d e hde hdiff hediff hactive ⟨hvw,huz⟩

#print axioms any_width_projected_loss_retains_all_but_one
#print axioms any_width_translated_cube_agrees_at_retained_active
#print axioms any_width_translated_cube_two_disagreements_impossible
#print axioms any_width_translated_slice_two_disagreements_distinct_owners

end OrderedEdgeColoring
end JSP000404Research
