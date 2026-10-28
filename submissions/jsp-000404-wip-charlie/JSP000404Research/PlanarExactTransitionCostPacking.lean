import JSP000404Research.PlanarLowSupportCardinalityPacking
import JSP000404Research.HighExponentTransitionPacking
import JSP000404Research.PlanarThreeCrowdedTopTinyGap
import Mathlib.Tactic

/-!
# Exact exponent price of support-one original centres

The true strict-transition certificate at a support-one centre costs
EXACTLY k+1 quotient units, not merely two when k>0.
Selecting certificates ONLY on the actual original low-support
subfamily therefore proves, without any synthetic credit,

  #(support<=2) + SUM_(support=1) exponent <= 2*n.

The n=3 exponent-two branch must therefore have at least N-4
original support-three centres, even if their gap intervals overlap.
This geometric obstruction is stronger than the earlier N-5
bound which used only the first extra unit.

These are still necessary structural statements; they do not exclude
the top-exponent configuration nor construct exterior Boolean holes.
-/

namespace JSP000404Research
open scoped BigOperators

/-- The exact exponent price of ORIGINAL support-one centres in the
strict-support arc packing budget. Other centres, including those
with quotient support >=3, are not assumed to be low support. -/
theorem planar_exact_low_support_transition_cost_le_two_n
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane}
    (hp : Function.Injective p)
    {lam t delta : ℝ} {n : ℕ}
    (hcap : AngleCap p lam)
    (hn : 1 ≤ n)
    (hdelta0 : 0 ≤ delta)
    (hdeltaHalf : delta < (1 : ℝ) / 2)
    (ht : t = (n : ℝ) + delta)
    (hlam : lam = Real.pi / t)
    (C : ∀ i : V, CentreProjectiveCycle hp i) :
    let I := {i : V // positiveSupport (centreQuotient (C i) t) ≤ 2}
    Fintype.card I +
      (∑ r : I,
        if positiveSupport (centreQuotient (C r) t) = 1 then
          centreExponent (C r) t else 0) ≤ 2 * n := by
  classical
  let I : Type _ :=
    {i : V // positiveSupport (centreQuotient (C i) t) ≤ 2}
  let extra : I → ℕ := fun r =>
    if positiveSupport (centreQuotient (C r) t) = 1 then
      centreExponent (C r) t else 0
  have htpos : 0 < t := by
    rw [ht]
    have hnreal : (0 : ℝ) < (n : ℝ) := by
      exact_mod_cast (show 0 < n by omega)
    linarith
  have htone : 1 ≤ t := by
    rw [ht]
    have hnreal : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    linarith
  let cert : ∀ r : I,
      HighExponentTransitionIntervalCertificate hp t (r : V) (C r) :=
    fun r => Classical.choose
      (exists_transitionIntervalCertificate_of_support_le_two
        hp hcap htpos htone hlam (r : V) (C r) r.property)
  have hpositive (r : I) : 1 ≤ (cert r).qe := by
    have hr : (cert r).qe ≠ 0 :=
      Classical.choose_spec
        (exists_transitionIntervalCertificate_of_support_le_two
          hp hcap htpos htone hlam (r : V) (C r) r.property)
    exact Nat.one_le_iff_ne_zero.mpr hr
  have hinj : Function.Injective (fun r : I => (r : V)) := by
    intro a b hab
    exact Subtype.ext hab
  have hpack : (∑ r : I, (cert r).qe) ≤ 2 * n :=
    highTransition_quotient_sum_le_two_n
      hp hn hdelta0 hdeltaHalf ht
      (fun r : I => (r : V)) hinj
      (fun r : I => C r) cert
  have hcost (r : I) :
      1 + extra r ≤ (cert r).qe := by
    by_cases hs : positiveSupport (centreQuotient (C r) t) = 1
    · have heq :
          (cert r).qe = centreExponent (C r) t + 1 :=
        highTransition_qe_eq_exponent_add_one_of_support_one
          (C r) (cert r) hs
      simp only [extra, if_pos hs]
      omega
    · simpa only [extra, if_neg hs, add_zero] using hpositive r
  have hsum :
      (∑ r : I, (1 + extra r)) ≤
        (∑ r : I, (cert r).qe) := by
    apply Finset.sum_le_sum
    intro r _
    exact hcost r
  have hcount :
      (∑ r : I, (1 + extra r)) =
        Fintype.card I + (∑ r : I, extra r) := by
    simp [Finset.sum_add_distrib]
  have hresult :
      Fintype.card I + (∑ r : I, extra r) ≤ 2 * n := by
    omega
  simpa [I, extra] using hresult

/-- A genuine original n=3 top exponent TWO consumes three transition
units by itself. Consequently its low-support companions consume
at most three other units, leaving at least N-4 high-support
original centres. The conclusion is structural, not a payment. -/
theorem planar_three_top_forces_high_support_plus_four_ge_card
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane}
    (hp : Function.Injective p)
    {lam t delta : ℝ}
    (hcap : AngleCap p lam)
    (hdelta0 : 0 ≤ delta)
    (hdeltaHalf : delta < (1 : ℝ) / 2)
    (ht : t = (3 : ℝ) + delta)
    (hlam : lam = Real.pi / t)
    (C : ∀ i : V, CentreProjectiveCycle hp i)
    (htop : ∃ i : V, centreExponent (C i) t = 2) :
    Fintype.card V ≤
      ((Finset.univ : Finset V).filter
        (fun i => 3 ≤ positiveSupport (centreQuotient (C i) t))).card + 4 := by
  classical
  let I : Type _ :=
    {i : V // positiveSupport (centreQuotient (C i) t) ≤ 2}
  let extra : I → ℕ := fun r =>
    if positiveSupport (centreQuotient (C r) t) = 1 then
      centreExponent (C r) t else 0
  let L : Finset V :=
    Finset.univ.filter (fun i =>
      positiveSupport (centreQuotient (C i) t) ≤ 2)
  let H : Finset V :=
    Finset.univ.filter (fun i =>
      3 ≤ positiveSupport (centreQuotient (C i) t))
  obtain ⟨i, hi⟩ := htop
  have hisupp : positiveSupport (centreQuotient (C i) t) = 1 :=
    (planar_three_top_centre_has_exact_unit_support
      (C i) hdelta0 hdeltaHalf ht hi).1
  let z : I := ⟨i, by omega⟩
  have hz : extra z = 2 := by
    simp [extra, z, hisupp, hi]
  have htwo : 2 ≤ (∑ r : I, extra r) := by
    have hsingle : extra z ≤ (∑ r : I, extra r) :=
      Finset.single_le_sum
        (f := extra) (fun _ _ => Nat.zero_le _)
        (Finset.mem_univ z)
    omega
  have hbudget :
      Fintype.card I + (∑ r : I, extra r) ≤ 6 := by
    have hh := planar_exact_low_support_transition_cost_le_two_n
      hp hcap (by decide : 1 ≤ (3 : ℕ))
      hdelta0 hdeltaHalf ht hlam C
    simpa [I, extra] using hh
  have hLow : Fintype.card I = L.card := by
    simp [I, L, Fintype.card_subtype]
  have hcomp : H = (Finset.univ : Finset V) \ L := by
    ext i
    simp only [H, L, Finset.mem_filter, Finset.mem_univ,
      true_and, Finset.mem_sdiff]
    omega
  have hpart : H.card + L.card = Fintype.card V := by
    have hc := Finset.card_sdiff_add_card_inter
      (Finset.univ : Finset V) L
    rw [← hcomp] at hc
    simpa using hc
  change Fintype.card V ≤ H.card + 4
  omega

/-- In a seven-or-more original-centre positive-strip configuration,
any actual top exponent forces at least THREE independent
high-support ORIGINAL vertices (not disjoint Boolean credits). -/
theorem planar_three_seven_top_forces_three_support_three_centres
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane}
    (hp : Function.Injective p)
    {lam t delta : ℝ}
    (hcap : AngleCap p lam)
    (hseven : 7 ≤ Fintype.card V)
    (hdelta0 : 0 ≤ delta)
    (hdeltaHalf : delta < (1 : ℝ) / 2)
    (ht : t = (3 : ℝ) + delta)
    (hlam : lam = Real.pi / t)
    (C : ∀ i : V, CentreProjectiveCycle hp i)
    (htop : ∃ i : V, centreExponent (C i) t = 2) :
    3 ≤ ((Finset.univ : Finset V).filter
      (fun i => 3 ≤ positiveSupport (centreQuotient (C i) t))).card := by
  have h := planar_three_top_forces_high_support_plus_four_ge_card
    hp hcap hdelta0 hdeltaHalf ht hlam C htop
  omega

#print axioms planar_exact_low_support_transition_cost_le_two_n
#print axioms planar_three_top_forces_high_support_plus_four_ge_card
#print axioms planar_three_seven_top_forces_three_support_three_centres

end JSP000404Research
