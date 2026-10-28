import JSP000404Research.PlanarThreeManyQuantitativeGapMultiplicity
import JSP000404Research.CentreExponentBounds
import JSP000404Research.AngleCapStrictProjectiveTheta
import Mathlib.Tactic

/-!
# Actual n=3 crowded TOP centre forces an even smaller gap

For N>=7 original AngleCap centres, an exponent-two centre has
EXACTLY ONE positive quotient with total quotient mass THREE.
The other N-2 original projective gaps have zero integer quotient,
are ALL strictly positive, and share only ONE scaled delta budget.
One real gap therefore obeys (N-2)*t*g <= delta.

This is a source-native geometric *necessary* condition for
the top-exponent branch of an n=3 overweight configuration.
No extra global hole credit, new axiom or stronger geometric
hypothesis is asserted.
-/

namespace JSP000404Research
open scoped BigOperators

/-- At t=3+delta, an original exponent-two centre is genuinely
saturated with exactly one nonzero quotient coordinate. -/
theorem planar_three_top_centre_has_exact_unit_support
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane} {hp : Function.Injective p}
    {i : V} (C : CentreProjectiveCycle hp i)
    {t delta : ℝ}
    (hdelta0 : 0 ≤ delta)
    (hdeltaHalf : delta < (1 : ℝ) / 2)
    (ht : t = (3 : ℝ) + delta)
    (htop : centreExponent C t = 2) :
    positiveSupport (centreQuotient C t) = 1 ∧
      (∑ r, centreQuotient C t r) = 3 := by
  classical
  let q := centreQuotient C t
  have hdelta1 : delta < 1 := by linarith
  have hbound : (∑ r, q r) ≤ 3 :=
    centreQuotient_function_sum_le_n C 3 delta t
      (by decide : 1 ≤ (3 : ℕ)) hdelta0 hdelta1 ht
  have hid : centreExponent C t + positiveSupport q = ∑ r, q r := by
    exact floorExcess_add_positiveSupport q
  have hspos : 0 < positiveSupport q := by
    by_contra hnot
    have hs0 : positiveSupport q = 0 := by omega
    have hq0 := positiveSupport_eq_zero_imp q hs0
    have he0 : centreExponent C t = 0 := by
      unfold centreExponent floorExcess
      simp [q, hq0]
    omega
  have hs : positiveSupport q = 1 := by omega
  have hsum : (∑ r, q r) = 3 := by omega
  exact ⟨hs, hsum⟩

/-- A crowded actual n=3 top centre of exponent two has N-2
strictly positive zero-quotient gaps, and at least one is so narrow
that its (N-2)-fold scaled width is <= the sole local delta.

This tightens the (N-4)-fold high-support conclusion specifically
for the remaining top-layer overweight motif. -/
theorem planar_three_crowded_top_forces_n_minus_two_tiny_gap
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane}
    (hp : Function.Injective p)
    {lam t delta : ℝ}
    (hcap : AngleCap p lam)
    (hcard : 7 ≤ Fintype.card V)
    (hdelta0 : 0 ≤ delta)
    (hdeltaHalf : delta < (1 : ℝ) / 2)
    (ht : t = (3 : ℝ) + delta)
    (hlam : lam = Real.pi / t)
    (C : ∀ i : V, CentreProjectiveCycle hp i)
    (i : V)
    (htop : centreExponent (C i) t = 2) :
    ∃ r : Fin (C i).gaps.length,
      centreQuotient (C i) t r = 0 ∧
      0 < (C i).gaps.get r ∧
      ((Fintype.card V - 2 : ℕ) : ℝ) *
        (t * (C i).gaps.get r) ≤ delta := by
  classical
  obtain ⟨hsup, hmass⟩ :=
    planar_three_top_centre_has_exact_unit_support
      (C i) hdelta0 hdeltaHalf ht htop
  have hother :
      Fintype.card (OtherVertex i) = Fintype.card V - 1 := by
    change Fintype.card {j : V // j ≠ i} = Fintype.card V - 1
    rw [Fintype.card_subtype_compl (fun j : V => j = i),
      Fintype.card_subtype_eq]
  have hraylen : (C i).rays.length = Fintype.card (OtherVertex i) := by
    rw [← List.toFinset_card_of_nodup (C i).nodup, (C i).complete]
    simp
  have hgaplen : (C i).gaps.length = Fintype.card V - 1 := by
    rw [(C i).gaps_length, hraylen, hother]
  let S : Finset (Fin (C i).gaps.length) :=
    Finset.univ.filter (fun r => centreQuotient (C i) t r = 0)
  have hzeros : S.card = Fintype.card V - 2 := by
    have hh :=
      quotient_zero_filter_card_eq_total_sub_support
        (centreQuotient (C i) t)
    have hbase : S.card = (C i).gaps.length - 1 := by
      simpa [S, hsup] using hh
    omega
  have htotal :
      (∑ r ∈ S, t * (C i).gaps.get r) ≤ delta := by
    simpa [S] using
      (saturated_centre_zero_gap_total_le_slack
        (C i) 3 hdelta0 ht hmass)
  obtain ⟨r, hr, hsmall⟩ :=
    exists_k_way_small_summand S
      (fun r => t * (C i).gaps.get r) delta
      (Fintype.card V - 2)
      (by omega) (by omega) hdelta0 htotal
  have hq : centreQuotient (C i) t r = 0 :=
    (Finset.mem_filter.mp hr).2
  have htpos : 0 < t := by rw [ht]; linarith
  have hlampos : 0 < lam := by
    rw [hlam]
    exact div_pos Real.pi_pos htpos
  have hgapPos : 0 < (C i).gaps.get r :=
    centreProjectiveCycle_gaps_pos_of_AngleCap
      hp hcap hlampos i (C i) _ (List.get_mem _ _)
  exact ⟨r, hq, hgapPos, hsmall⟩

#print axioms planar_three_top_centre_has_exact_unit_support
#print axioms planar_three_crowded_top_forces_n_minus_two_tiny_gap

end JSP000404Research
