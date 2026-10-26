import JSP000404Research.PlanarExactTransitionCostPacking
import JSP000404Research.PlanarThreeManyQuantitativeGapMultiplicity
import Mathlib.Tactic

/-!
# Genuine n=3 top+next support-one centres jointly spend 5 of 6 transition units

This strengthens the single-top original support packing statement
in the exact difficult top+next subcase. A top exponent-two centre
with support one has cost 1+2=3; an additional, distinct exponent-one
support-one centre costs 1+1=2. Both are ORIGINAL vertices.
Thus at most three original centres can have support <=2.

Every remaining original centre has support exactly three and exponent
zero by the existing rigid n=3 quotient structure. Nothing here
identifies projective gap witnesses with actual Boolean exterior holes;
it is a necessary geometry condition, not a full capacity proof.
-/

namespace JSP000404Research
open scoped BigOperators

/-- Under ACTUAL n=3 AngleCap, a top and a distinct next exponent-one
centre with support ONE force all but at most three original
vertices to have support >=3. -/
theorem planar_three_top_next_support_one_forces_high_support_plus_three
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
    (s a : V)
    (hs : centreExponent (C s) t = 2)
    (ha : centreExponent (C a) t = 1)
    (haSupport : positiveSupport (centreQuotient (C a) t) = 1) :
    Fintype.card V ≤
      ((Finset.univ : Finset V).filter
        (fun i => 3 ≤ positiveSupport (centreQuotient (C i) t))).card + 3 := by
  classical
  have hne : s ≠ a := by
    intro h
    rw [h] at hs
    omega
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
  have hsSupport : positiveSupport (centreQuotient (C s) t) = 1 :=
    (planar_three_top_centre_has_exact_unit_support
      (C s) hdelta0 hdeltaHalf ht hs).1
  let zs : I := ⟨s, by omega⟩
  let za : I := ⟨a, by omega⟩
  have hzs : extra zs = 2 := by
    simp [extra, zs, hsSupport, hs]
  have hza : extra za = 1 := by
    simp [extra, za, haSupport, ha]
  have hzsne : zs ≠ za := by
    intro h
    exact hne (congrArg Subtype.val h)
  have htwo :
      extra zs + extra za ≤ (∑ r : I, extra r) := by
    have hle :
        (∑ r ∈ ({zs, za} : Finset I), extra r) ≤
          (∑ r : I, extra r) :=
      Finset.sum_le_sum_of_subset_of_nonneg
        (Finset.subset_univ _)
        (by intro i _ _; exact Nat.zero_le _)
    have hpair :
        (∑ r ∈ ({zs, za} : Finset I), extra r) =
          extra zs + extra za := by
      simp [hzsne, Ne.symm hzsne, add_comm]
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
  change Fintype.card V ≤ H.card + 3
  omega

/-- In the particular seven-or-more ORIGINAL-centre top+next support-one
configuration, at least FOUR distinct original centres are high support.
They are not claimed to provide independent Boolean hole credits. -/
theorem planar_three_seven_top_next_support_one_forces_four_high
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
    (s a : V)
    (hs : centreExponent (C s) t = 2)
    (ha : centreExponent (C a) t = 1)
    (haSupport : positiveSupport (centreQuotient (C a) t) = 1) :
    4 ≤ ((Finset.univ : Finset V).filter
      (fun i => 3 ≤ positiveSupport (centreQuotient (C i) t))).card := by
  have h := planar_three_top_next_support_one_forces_high_support_plus_three
    hp hcap hdelta0 hdeltaHalf ht hlam C s a hs ha haSupport
  omega

#print axioms planar_three_top_next_support_one_forces_high_support_plus_three
#print axioms planar_three_seven_top_next_support_one_forces_four_high

end JSP000404Research
