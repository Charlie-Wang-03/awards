import JSP000404Research.PlanarThreeSevenCentreTripleUnitNecessity
import JSP000404Research.AngleCapStrictProjectiveTheta
import Mathlib.Tactic

/-!
# Seven genuine n=3 centres: at least THREE separate real zero-quotient gaps

The true original AngleCap seven-centre theorem produces a center with
three unit-positive projective quotients and one global delta remainder
budget. There are at least six original projective gaps at that centre.

Therefore THREE OR MORE different original gap indices have quotient
zero. Each gap is strictly positive under AngleCap, and their COMBINED
scaled width (not merely individual upper bounds) is at most delta.

This is a genuine positive-delta geometric necessary obstruction for
the still-open seven-plus-centre n=3 lower strip, with no synthetic
hole, global payment assumption, or new sorry.
-/

namespace JSP000404Research
open scoped BigOperators

/-- For any finite quotient, the number of zero coordinates is exactly
total index count minus the positive support. -/
theorem quotient_zero_filter_card_eq_total_sub_support
    {I : Type*} [Fintype I] [DecidableEq I]
    (q : I → ℕ) :
    (Finset.univ.filter (fun i => q i = 0)).card =
      Fintype.card I - positiveSupport q := by
  classical
  have hpos :
      positiveSupport q =
        (Finset.univ.filter (fun i => q i ≠ 0)).card := by
    unfold positiveSupport
    simp [Finset.sum_ite]
  have hsplit :
      (Finset.univ.filter (fun i => q i = 0)).card +
        (Finset.univ.filter (fun i => q i ≠ 0)).card =
          Fintype.card I := by
    simpa using
      (Finset.filter_card_add_filter_neg_card_eq_card
        (s := (Finset.univ : Finset I)) (p := fun i => q i = 0))
  omega

/-- Actual seven-plus-centre AngleCap geometry forces at least three
distinct positive ZERO-QUOTIENT gaps at some original center, whose
TOTAL scaled length shares a single delta budget. -/
theorem planar_three_seven_forces_three_positive_zero_gaps_with_total_slack
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
    (C : ∀ i : V, CentreProjectiveCycle hp i) :
    ∃ i : V,
      3 ≤ ((Finset.univ : Finset (Fin (C i).gaps.length)).filter
        (fun r => centreQuotient (C i) t r = 0)).card ∧
      (∀ r : Fin (C i).gaps.length,
        centreQuotient (C i) t r = 0 →
          0 < (C i).gaps.get r) ∧
      (∑ r ∈ (Finset.univ.filter
        (fun r : Fin (C i).gaps.length =>
          centreQuotient (C i) t r = 0)),
          t * (C i).gaps.get r) ≤ delta := by
  classical
  obtain ⟨i, _hk, hsupport, _hmass, _hunit,
      _hunitCount, hslack⟩ :=
    planar_three_seven_centres_force_saturated_triple_unit_and_slack
      hp hcap hcard hdelta0 hdeltaHalf ht hlam C
  have hother :
      Fintype.card (OtherVertex i) = Fintype.card V - 1 := by
    change Fintype.card {j : V // j ≠ i} = Fintype.card V - 1
    rw [Fintype.card_subtype_compl (fun j : V => j = i),
      Fintype.card_subtype_eq]
  have hraylen : (C i).rays.length = Fintype.card (OtherVertex i) := by
    rw [← List.toFinset_card_of_nodup (C i).nodup, (C i).complete]
    simp
  have hgapge :
      6 ≤ (C i).gaps.length := by
    rw [(C i).gaps_length, hraylen, hother]
    omega
  have hzeros :
      3 ≤ ((Finset.univ : Finset (Fin (C i).gaps.length)).filter
        (fun r => centreQuotient (C i) t r = 0)).card := by
    rw [quotient_zero_filter_card_eq_total_sub_support]
    simpa only [Fintype.card_fin, hsupport] using
      (show 3 ≤ (C i).gaps.length - 3 by omega)
  have htpos : 0 < t := by
    rw [ht]
    linarith
  have hlampos : 0 < lam := by
    rw [hlam]
    exact div_pos Real.pi_pos htpos
  refine ⟨i, hzeros, ?_, hslack⟩
  intro r _hr
  exact centreProjectiveCycle_gaps_pos_of_AngleCap
    hp hcap hlampos i (C i) _ (List.get_mem _ _)

#print axioms quotient_zero_filter_card_eq_total_sub_support
#print axioms planar_three_seven_forces_three_positive_zero_gaps_with_total_slack

end JSP000404Research
