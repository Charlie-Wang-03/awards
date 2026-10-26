import JSP000404Research.PlanarThreeManyQuantitativeGapMultiplicity
import JSP000404Research.ThreeFiveSupportThreeRigidity
import Mathlib.Tactic

/-!
# Exact ORIGINAL three-scale dyadic residual, not extra credit

The original n=3 lower-branch total is exactly
  |V| + sum over ACTUAL low-support centres i of (2^k(i)-1).
Every support>=3 centre has k(i)=0 by an existing kernel-checked
rigidity theorem; no synthetic Boolean hole, debt payment, or
unreserved profile surplus is introduced.

Thus at n=3 the original full dyadic capacity <=8 is EQUIVALENT
to the displayed explicit nonnegative low-support residual <=8.
This is a statement-level reduction, not a proof of that final
inequality for arbitrary planar configurations.
-/

namespace JSP000404Research
open scoped BigOperators

/-- All n=3 excess above one per original centre is concentrated
exactly on the true original centres with quotient support <=2. -/
theorem planar_three_dyadic_eq_original_card_add_low_support_excess
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane}
    (hp : Function.Injective p)
    {t delta : ℝ}
    (hdelta0 : 0 ≤ delta)
    (hdeltaHalf : delta < (1 : ℝ) / 2)
    (ht : t = (3 : ℝ) + delta)
    (C : ∀ i : V, CentreProjectiveCycle hp i) :
    (∑ i : V, 2 ^ centreExponent (C i) t) =
      Fintype.card V +
      (∑ i ∈ (Finset.univ.filter
        (fun i : V => positiveSupport (centreQuotient (C i) t) ≤ 2)),
        (2 ^ centreExponent (C i) t - 1)) := by
  classical
  let L : Finset V :=
    Finset.univ.filter (fun i =>
      positiveSupport (centreQuotient (C i) t) ≤ 2)
  have highzero (i : V) (hi : i ∉ L) :
      centreExponent (C i) t = 0 := by
    have hnot : ¬ positiveSupport (centreQuotient (C i) t) ≤ 2 := by
      simpa [L] using hi
    have hthree : 3 ≤ positiveSupport (centreQuotient (C i) t) := by
      omega
    exact (three_scale_high_support_exact_rigidity
      (C i) hdelta0 hdeltaHalf ht hthree).1
  have hfilter :
      (∑ i : V, (2 ^ centreExponent (C i) t - 1)) =
      (∑ i ∈ L, (2 ^ centreExponent (C i) t - 1)) := by
    calc
      (∑ i : V, (2 ^ centreExponent (C i) t - 1)) =
        ∑ i : V, if i ∈ L then (2 ^ centreExponent (C i) t - 1) else 0 := by
          apply Finset.sum_congr rfl
          intro i _
          by_cases hi : i ∈ L
          · simp [hi]
          · simp [hi, highzero i hi]
      _ = (∑ i ∈ L, (2 ^ centreExponent (C i) t - 1)) := by
          simp [Finset.sum_ite]
  have hsplit :
      (∑ i : V, 2 ^ centreExponent (C i) t) =
        Fintype.card V +
          (∑ i : V, (2 ^ centreExponent (C i) t - 1)) := by
    calc
      (∑ i : V, 2 ^ centreExponent (C i) t) =
          ∑ i : V, ((2 ^ centreExponent (C i) t - 1) + 1) := by
            apply Finset.sum_congr rfl
            intro i _
            have hpos : 0 < (2 : ℕ) ^ centreExponent (C i) t := by
              positivity
            omega
      _ = (∑ i : V, (2 ^ centreExponent (C i) t - 1)) +
            (∑ _i : V, (1 : ℕ)) := by
            rw [Finset.sum_add_distrib]
      _ = Fintype.card V +
            (∑ i : V, (2 ^ centreExponent (C i) t - 1)) := by
            simp [add_comm]
  change (∑ i : V, 2 ^ centreExponent (C i) t) =
    Fintype.card V + (∑ i ∈ L, 2 ^ centreExponent (C i) t - 1)
  rw [hsplit, hfilter]

/-- Exact equivalence: for genuine n=3 projective cycles, the
full dyadic capacity is *precisely* a count-plus-low-support-excess
budget. No unjustified positivity or non-reuse assumption is needed. -/
theorem planar_three_dyadic_le_eight_iff_low_support_residual
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane}
    (hp : Function.Injective p)
    {t delta : ℝ}
    (hdelta0 : 0 ≤ delta)
    (hdeltaHalf : delta < (1 : ℝ) / 2)
    (ht : t = (3 : ℝ) + delta)
    (C : ∀ i : V, CentreProjectiveCycle hp i) :
    ((∑ i : V, 2 ^ centreExponent (C i) t) ≤ 8) ↔
      (Fintype.card V +
        (∑ i ∈ (Finset.univ.filter
          (fun i : V => positiveSupport (centreQuotient (C i) t) ≤ 2)),
          (2 ^ centreExponent (C i) t - 1)) ≤ 8) := by
  rw [planar_three_dyadic_eq_original_card_add_low_support_excess
    hp hdelta0 hdeltaHalf ht C]

/-- Under the original n=3 capacity, nine or more ORIGINAL
centres are impossible. This is a conditional consequence of the
desired capacity, not a proof that AngleCap rules them out. -/
theorem planar_three_dyadic_capacity_implies_card_le_eight
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane}
    (hp : Function.Injective p)
    {t delta : ℝ}
    (hdelta0 : 0 ≤ delta)
    (hdeltaHalf : delta < (1 : ℝ) / 2)
    (ht : t = (3 : ℝ) + delta)
    (C : ∀ i : V, CentreProjectiveCycle hp i)
    (hcap : (∑ i : V, 2 ^ centreExponent (C i) t) ≤ 8) :
    Fintype.card V ≤ 8 := by
  have h := (planar_three_dyadic_le_eight_iff_low_support_residual
    hp hdelta0 hdeltaHalf ht C).mp hcap
  omega

#print axioms planar_three_dyadic_eq_original_card_add_low_support_excess
#print axioms planar_three_dyadic_le_eight_iff_low_support_residual
#print axioms planar_three_dyadic_capacity_implies_card_le_eight

end JSP000404Research
