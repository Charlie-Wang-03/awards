import JSP000404Research.NineCentreTopFourthLayerCapacity
import Mathlib.Tactic

/-!
# General top/no-next fourth-layer census from genuine AngleCap geometry

A top exponent n-1 centre is unique once there are >=3 vertices.
If n>=5, no centre has exponent n-2, and every n-3 centre has
genuine quotient support one, there is at most ONE such third-layer
centre, by a separately proved planar geometric exclusion.

The four-layer dyadic census therefore closes whenever
    |V| + #{i | centreExponent i = n-4} <= 14.

This extends the earlier fixed nine-centre + at most five fourth-layer
result to ALL finite sizes (including ten centres plus <=4 fourth-layer
centres, eleven plus <=3, etc.). The census premise remains explicit:
it is NOT derived universally from AngleCap.

No global nonreusable external-TRUE-hole payment is assumed.
-/

namespace JSP000404Research

open scoped BigOperators

theorem planar_top_no_next_support_one_fourth_trade_capacity
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane}
    (hp : Function.Injective p)
    {lam t delta : ℝ} {n : ℕ}
    (hcap : AngleCap p lam)
    (hcard3 : 3 ≤ Fintype.card V)
    (hn : 5 ≤ n)
    (hdelta0 : 0 ≤ delta)
    (hdeltaHalf : delta < (1 : ℝ) / 2)
    (ht : t = (n : ℝ) + delta)
    (hlam : lam = Real.pi / t)
    (C : ∀ i : V, CentreProjectiveCycle hp i)
    (s : V)
    (hs : centreExponent (C s) t = n - 1)
    (hnoNext : ∀ i : V, centreExponent (C i) t ≠ n - 2)
    (hThirdSupportOne : ∀ i : V,
      centreExponent (C i) t = n - 3 →
      positiveSupport (centreQuotient (C i) t) = 1)
    (hTradeFourth :
      Fintype.card V +
        ((Finset.univ : Finset V).filter
          (fun i => centreExponent (C i) t = n - 4)).card ≤ 14) :
    (∑ i : V, 2 ^ centreExponent (C i) t) ≤ 2 ^ n := by
  classical
  let k : V → ℕ := fun i => centreExponent (C i) t
  let H : Finset V := (Finset.univ : Finset V).filter (fun i => k i = n - 1)
  let N : Finset V := (Finset.univ : Finset V).filter (fun i => k i = n - 2)
  let T : Finset V := (Finset.univ : Finset V).filter (fun i => k i = n - 3)
  let F : Finset V := (Finset.univ : Finset V).filter (fun i => k i = n - 4)
  have htopEq : H = {s} := by
    ext i
    simp only [H, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_singleton]
    constructor
    · intro hi
      exact topExponent_eq_fixed_top hp hcap hcard3
        (by omega : 3 ≤ n) hdelta0 hdeltaHalf ht hlam C s i hs hi
    · intro hi
      subst i
      exact hs
  have htopCard : H.card = 1 := by simp [htopEq]
  have hnextCard : N.card = 0 := by simp [N, k, hnoNext]
  have hthirdCard : T.card ≤ 1 := by
    have hsub : T ⊆
        (Finset.univ : Finset V).filter
          (fun i => i ≠ s ∧
            centreExponent (C i) t = n - 3 ∧
            positiveSupport (centreQuotient (C i) t) = 1) := by
      intro i hi
      have hk : centreExponent (C i) t = n - 3 :=
        (Finset.mem_filter.mp hi).2
      have his : i ≠ s := by
        intro he
        subst i
        omega
      exact Finset.mem_filter.mpr
        ⟨Finset.mem_univ i, ⟨his, hk, hThirdSupportOne i hk⟩⟩
    exact (Finset.card_le_card hsub).trans
      (top_third_support_one_count_le_one_n_ge_five
        hp hcap hn hdelta0 hdeltaHalf ht hlam C s hs)
  have hdelta1 : delta < 1 := by linarith
  have hmax : ∀ i : V, k i ≤ n - 1 := by
    intro i
    change centreExponent (C i) t ≤ n - 1
    have hlt : centreExponent (C i) t < n :=
      centreExponent_lt_n (C i) n delta t
        (by omega : 1 ≤ n) hdelta0 hdelta1 ht
    omega
  have htrade :
      Fintype.card V + 15 * H.card + 7 * N.card +
        3 * T.card + F.card ≤ 32 := by
    have hcount : Fintype.card V + F.card ≤ 14 := by
      simpa only [F, k] using hTradeFourth
    omega
  exact dyadic_capacity_of_four_layer_count_tradeoff k n hn hmax
    (by simpa only [H,N,T,F,k] using htrade)

/-- Any overweight true planar top/no-next configuration whose
third-layer centres all have support one must violate the exact
cardinality-plus-fourth-layer budget. Unlike the earlier nine-centre
version, this necessary obstruction does not assume |V|≤9. -/
theorem planar_top_no_next_support_one_overweight_requires_fourth_trade_excess
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane}
    (hp : Function.Injective p)
    {lam t delta : ℝ} {n : ℕ}
    (hcap : AngleCap p lam)
    (hcard3 : 3 ≤ Fintype.card V)
    (hn : 5 ≤ n)
    (hdelta0 : 0 ≤ delta)
    (hdeltaHalf : delta < (1 : ℝ) / 2)
    (ht : t = (n : ℝ) + delta)
    (hlam : lam = Real.pi / t)
    (C : ∀ i : V, CentreProjectiveCycle hp i)
    (s : V)
    (hs : centreExponent (C s) t = n - 1)
    (hnoNext : ∀ i : V, centreExponent (C i) t ≠ n - 2)
    (hThirdSupportOne : ∀ i : V,
      centreExponent (C i) t = n - 3 →
      positiveSupport (centreQuotient (C i) t) = 1)
    (hover : 2 ^ n < ∑ i : V, 2 ^ centreExponent (C i) t) :
    14 < Fintype.card V +
        ((Finset.univ : Finset V).filter
          (fun i => centreExponent (C i) t = n - 4)).card := by
  classical
  by_contra hnot
  have hTrade : Fintype.card V +
      ((Finset.univ : Finset V).filter
        (fun i => centreExponent (C i) t = n - 4)).card ≤ 14 := by omega
  have hcapacity :=
    planar_top_no_next_support_one_fourth_trade_capacity
      hp hcap hcard3 hn hdelta0 hdeltaHalf ht hlam
      C s hs hnoNext hThirdSupportOne hTrade
  exact (not_lt_of_ge hcapacity) hover

/-- An unrestricted-cardinality ACTUAL geometric overweight dichotomy
(with a true top n-1 centre and no n-2 centres).
Either a true n-3 centre has quotient support 2/3, or the
original vertex count plus exact n-4 count is at least 15.
No upper bound on ambient vertex count is required. -/
theorem planar_top_no_next_overweight_support_two_three_or_fourth_trade_excess
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane}
    (hp : Function.Injective p)
    {lam t delta : ℝ} {n : ℕ}
    (hcap : AngleCap p lam)
    (hcard3 : 3 ≤ Fintype.card V)
    (hn : 5 ≤ n)
    (hdelta0 : 0 ≤ delta)
    (hdeltaHalf : delta < (1 : ℝ) / 2)
    (ht : t = (n : ℝ) + delta)
    (hlam : lam = Real.pi / t)
    (C : ∀ i : V, CentreProjectiveCycle hp i)
    (s : V)
    (hs : centreExponent (C s) t = n - 1)
    (hnoNext : ∀ i : V, centreExponent (C i) t ≠ n - 2)
    (hover : 2 ^ n < ∑ i : V, 2 ^ centreExponent (C i) t) :
    (∃ i : V, centreExponent (C i) t = n - 3 ∧
      (positiveSupport (centreQuotient (C i) t) = 2 ∨
       positiveSupport (centreQuotient (C i) t) = 3)) ∨
    14 < Fintype.card V +
      ((Finset.univ : Finset V).filter
        (fun i => centreExponent (C i) t = n - 4)).card := by
  classical
  by_cases hfourth :
      Fintype.card V +
        ((Finset.univ : Finset V).filter
          (fun i => centreExponent (C i) t = n - 4)).card ≤ 14
  · left
    by_contra hnone
    have hdelta1 : delta < 1 := by linarith
    have hThirdSupportOne :
        ∀ i : V, centreExponent (C i) t = n - 3 →
          positiveSupport (centreQuotient (C i) t) = 1 := by
      intro i hi
      rcases concrete_deficit_three_structure
          (C i) (by omega : 4 ≤ n) hdelta0 hdelta1 ht hi
        with h1 | h2 | h3
      · exact h1.1
      · exact False.elim (hnone ⟨i, hi, Or.inl h2.1⟩)
      · exact False.elim (hnone ⟨i, hi, Or.inr h3.1⟩)
    have hcapacity :=
      planar_top_no_next_support_one_fourth_trade_capacity
        hp hcap hcard3 hn hdelta0 hdeltaHalf ht hlam
        C s hs hnoNext hThirdSupportOne hfourth
    exact (not_lt_of_ge hcapacity) hover
  · right
    omega

#print axioms planar_top_no_next_support_one_fourth_trade_capacity
#print axioms planar_top_no_next_support_one_overweight_requires_fourth_trade_excess
#print axioms planar_top_no_next_overweight_support_two_three_or_fourth_trade_excess

end JSP000404Research
