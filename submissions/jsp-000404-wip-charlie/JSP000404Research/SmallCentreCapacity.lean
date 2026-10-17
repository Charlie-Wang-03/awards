import JSP000404Research.CentreExponentBounds
import JSP000404Research.TwoCentreTerminal
import JSP000404Research.GenericTopExponentMultiplicity
import Mathlib.Tactic

/-!
# Closed dyadic capacity for at most two ORIGINAL actual centres

Each genuine centre exponent satisfies k<n for t=n+delta with 0<=delta<1.
For a finite configuration with at most two centres this gives
sum 2^k <= card(V)*2^(n-1) <= 2^n.
Unlike the general proof, no cross-source Boolean payment is needed.
-/

namespace JSP000404Research

theorem small_centre_card_le_two_dyadic_capacity
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane}
    (hp : Function.Injective p)
    {t delta : ℝ} {n : ℕ}
    (hcard : Fintype.card V ≤ 2)
    (hn : 1 ≤ n)
    (hdelta0 : 0 ≤ delta)
    (hdeltaHalf : delta < (1 : ℝ) / 2)
    (ht : t = (n : ℝ) + delta)
    (C : ∀ i : V, CentreProjectiveCycle hp i) :
    (∑ i : V, 2 ^ centreExponent (C i) t) ≤ 2 ^ n := by
  have hdelta1 : delta < 1 := by linarith
  have hpoint : ∀ i : V,
      2 ^ centreExponent (C i) t ≤ 2 ^ (n - 1) := by
    intro i
    have hexp :
        centreExponent (C i) t < n :=
      centreExponent_lt_n
        (C i) n delta t hn hdelta0 hdelta1 ht
    have hle : centreExponent (C i) t ≤ n - 1 := by omega
    exact Nat.pow_le_pow_right (by norm_num : 0 < 2) hle
  have hsum :
      (∑ i : V, 2 ^ centreExponent (C i) t)
        ≤ Fintype.card V * 2 ^ (n - 1) := by
    calc
      (∑ i : V, 2 ^ centreExponent (C i) t)
          ≤ ∑ _i : V, 2 ^ (n - 1) := by
            apply Finset.sum_le_sum
            intro i _
            exact hpoint i
      _ = Fintype.card V * 2 ^ (n - 1) := by simp
  have htwo :
      Fintype.card V * 2 ^ (n - 1)
        ≤ 2 * 2 ^ (n - 1) :=
    Nat.mul_le_mul_right _ hcard
  rw [two_centre_terminal_weight hn] at htwo
  exact hsum.trans htwo

namespace ProjectionOrdered

theorem planar_lower_branch_card_le_two_dyadic_capacity
    {V : Type*} [Fintype V]
    {p : V → Plane}
    (hp : Function.Injective p)
    {t delta : ℝ} {n : ℕ}
    (hcard : Fintype.card (ProjectionOrdered V) ≤ 2)
    (hn : 1 ≤ n)
    (hdelta0 : 0 ≤ delta)
    (hdeltaHalf : delta < (1 : ℝ) / 2)
    (ht : t = (n : ℝ) + delta)
    (cycles :
      letI : LinearOrder (ProjectionOrdered V) := projectionLinearOrder hp
      ∀ i : ProjectionOrdered V,
        CentreProjectiveCycle (reindexedPoint_injective hp) i) :
    letI : LinearOrder (ProjectionOrdered V) := projectionLinearOrder hp
    (∑ i : ProjectionOrdered V,
      2 ^ centreExponent (cycles i) t) ≤ 2 ^ n := by
  letI : LinearOrder (ProjectionOrdered V) := projectionLinearOrder hp
  exact small_centre_card_le_two_dyadic_capacity
    (reindexedPoint_injective hp)
    hcard hn hdelta0 hdeltaHalf ht cycles

#print axioms small_centre_card_le_two_dyadic_capacity
#print axioms planar_lower_branch_card_le_two_dyadic_capacity

end ProjectionOrdered
end JSP000404Research
