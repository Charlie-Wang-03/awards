import JSP000404Research.TopLayerThreeLevelDyadicCapacity
import JSP000404Research.ThirdLayerTwoSupportOneExclusion
import JSP000404Research.FiveCentreNoSecondLayerCapacity
import Mathlib.Tactic

/-!
# Genuine seven-centre top/no-next support-one geometry closes capacity

This corollary combines TWO certified independent ingredients:
(1) planar top-centre sharpness excludes two other n-3 support-one centres
    for n>=5 (no total vertex cardinality hypothesis);
(2) a top-inclusive weighted dyadic profile budget.

For 3<=|V|<=7, a top exponent n-1, no exponent n-2,
and every exponent n-3 centre having quotient support one,
the top is unique and the third-layer count is <=1.
Thus m+7*r+3*q+u<=7+7+0+1=15<=16.
No six-source TRUE-hole payment is invoked.
-/

namespace JSP000404Research
open scoped BigOperators

theorem planar_eight_centre_top_no_next_third_support_one_capacity
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane}
    (hp : Function.Injective p)
    {lam t delta : ℝ} {n : ℕ}
    (hcap : AngleCap p lam)
    (hcard3 : 3 ≤ Fintype.card V)
    (hcard8 : Fintype.card V ≤ 8)
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
      positiveSupport (centreQuotient (C i) t) = 1) :
    (∑ i : V, 2 ^ centreExponent (C i) t) ≤ 2 ^ n := by
  classical
  let H : Finset V := (Finset.univ : Finset V).filter
    (fun i => centreExponent (C i) t = n - 1)
  let M : Finset V := (Finset.univ : Finset V).filter
    (fun i => centreExponent (C i) t = n - 2)
  let L : Finset V := (Finset.univ : Finset V).filter
    (fun i => centreExponent (C i) t = n - 3)
  have hTopEq : H = {s} := by
    ext i
    simp only [H, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_singleton]
    constructor
    · intro hi
      exact topExponent_eq_fixed_top
        hp hcap hcard3 (by omega : 3 ≤ n)
        hdelta0 hdeltaHalf ht hlam C s i hs hi
    · intro hi
      subst i
      exact hs
  have hTopCard : H.card = 1 := by simp [hTopEq]
  have hNextCard : M.card = 0 := by
    apply Finset.card_eq_zero.mpr
    apply Finset.eq_empty_iff_forall_not_mem.mpr
    intro i hi
    exact hnoNext i ((Finset.mem_filter.mp hi).2)
  have hThirdCard : L.card ≤ 1 := by
    have hsubset : L ⊆
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
    exact (Finset.card_le_card hsubset).trans
      (top_third_support_one_count_le_one_n_ge_five
        hp hcap hn hdelta0 hdeltaHalf ht hlam C s hs)
  have htrade : Fintype.card V +
      7 * H.card + 3 * M.card + L.card ≤ 16 := by
    omega
  exact planar_top_three_layer_count_tradeoff_capacity
    hp hcap (by omega : 4 ≤ n) hdelta0 hdeltaHalf ht hlam C
    (by simpa [H,M,L] using htrade)

/-- The original seven-centre statement follows immediately from the
strictly stronger eight-centre actual planar capacity certificate. -/
theorem planar_seven_centre_top_no_next_third_support_one_capacity
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane}
    (hp : Function.Injective p)
    {lam t delta : ℝ} {n : ℕ}
    (hcap : AngleCap p lam)
    (hcard3 : 3 ≤ Fintype.card V)
    (hcard7 : Fintype.card V ≤ 7)
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
      positiveSupport (centreQuotient (C i) t) = 1) :
    (∑ i : V, 2 ^ centreExponent (C i) t) ≤ 2 ^ n := by
  exact planar_eight_centre_top_no_next_third_support_one_capacity
    hp hcap hcard3 (by omega : Fintype.card V ≤ 8)
    hn hdelta0 hdeltaHalf ht hlam C s hs hnoNext hThirdSupportOne

#print axioms planar_eight_centre_top_no_next_third_support_one_capacity
#print axioms planar_seven_centre_top_no_next_third_support_one_capacity

end JSP000404Research
