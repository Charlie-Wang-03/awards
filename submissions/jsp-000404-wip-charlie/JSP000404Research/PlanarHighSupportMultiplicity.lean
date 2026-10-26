import JSP000404Research.PlanarLowSupportCardinalityPacking
import Mathlib.Tactic

/-!
# Quantitative high-support multiplicity in genuine planar AngleCap geometry

At any lower-strip scale t = n + delta with 0 <= delta < 1/2,
the original low-support vertices (quotient support <= 2) account
for at most 2*n centres, even if the ambient geometry contains
high-support centres. Consequently at least card V - 2*n
ORIGINAL centres have positive quotient support >= 3.

For n=3, this upgrades the earlier seven-centre existence
pigeonhole to a quantitative multiplicity inequality. It is a
necessary structural condition, NOT a global dyadic-payment proof.
-/

namespace JSP000404Research

/-- The number of original centres with support >= 3 is at least
the total original-centre count minus the 2*n low-support capacity.
High-support centres are not assumed to have disjoint slots. -/
theorem planar_high_support_card_add_two_n_ge_total
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
    ((Finset.univ : Finset V).filter
      (fun i => 3 ≤ positiveSupport (centreQuotient (C i) t))).card
        + 2 * n ≥ Fintype.card V := by
  classical
  let L : Finset V :=
    Finset.univ.filter (fun i =>
      positiveSupport (centreQuotient (C i) t) ≤ 2)
  let H : Finset V :=
    Finset.univ.filter (fun i =>
      3 ≤ positiveSupport (centreQuotient (C i) t))
  have hlow : L.card ≤ 2 * n := by
    simpa [L, Fintype.card_subtype] using
      (planar_low_support_subfamily_card_le_two_n
        hp hcap hn hdelta0 hdeltaHalf ht hlam C)
  have hcomp : H = (Finset.univ : Finset V) \\ L := by
    ext i
    simp only [H, L, Finset.mem_filter, Finset.mem_univ,
      true_and, Finset.mem_sdiff]
    omega
  have hpart : H.card + L.card = Fintype.card V := by
    have hc :=
      Finset.card_sdiff_add_card_inter (Finset.univ : Finset V) L
    rw [← hcomp] at hc
    simpa using hc
  change H.card + 2 * n ≥ Fintype.card V
  omega

/-- At scale 3+delta, high-support centres make up all but at
most six original centres, regardless of ambient cardinality. -/
theorem planar_three_high_support_card_add_six_ge_total
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane}
    (hp : Function.Injective p)
    {lam t delta : ℝ}
    (hcap : AngleCap p lam)
    (hdelta0 : 0 ≤ delta)
    (hdeltaHalf : delta < (1 : ℝ) / 2)
    (ht : t = (3 : ℝ) + delta)
    (hlam : lam = Real.pi / t)
    (C : ∀ i : V, CentreProjectiveCycle hp i) :
    ((Finset.univ : Finset V).filter
      (fun i => 3 ≤ positiveSupport (centreQuotient (C i) t))).card
        + 6 ≥ Fintype.card V := by
  simpa using
    (planar_high_support_card_add_two_n_ge_total
      hp hcap (by decide : 1 ≤ (3 : ℕ))
      hdelta0 hdeltaHalf ht hlam C)

#print axioms planar_high_support_card_add_two_n_ge_total
#print axioms planar_three_high_support_card_add_six_ge_total

end JSP000404Research
