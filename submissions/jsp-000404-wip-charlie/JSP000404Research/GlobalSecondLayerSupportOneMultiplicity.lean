import JSP000404Research.SecondLayerNoTopReduction
import JSP000404Research.GenericTopExponentMultiplicity
import Mathlib.Tactic

/-!
# Global second-layer support-one multiplicity bound

The three-centre transition-quotient packing obstruction, already proved
in SecondLayerNoTopReduction, forbids three distinct deficit-two
support-one centres when n >= 4. This file upgrades the chosen-triple
obstruction into a genuine global finite-cardinality bound (<= 2)
and transfers it to the exact projection-ordered planar indexing.

This is valid whether or not a top exponent is present. It is a
restriction on a genuine geometric subfamily, not on all second-layer
centres and not a solution to the remaining six-source global payment.
-/

namespace JSP000404Research

theorem actual_secondLayer_supportOne_card_le_two
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane}
    (hp : Function.Injective p)
    {lam t delta : ℝ} {n : ℕ}
    (hcap : AngleCap p lam)
    (hn4 : 4 ≤ n)
    (hdelta0 : 0 ≤ delta)
    (hdeltaHalf : delta < (1 : ℝ) / 2)
    (ht : t = (n : ℝ) + delta)
    (hlam : lam = Real.pi / t)
    (C : ∀ i : V, CentreProjectiveCycle hp i) :
    ((Finset.univ : Finset V).filter
      (fun i =>
        centreExponent (C i) t = n - 2 ∧
        positiveSupport (centreQuotient (C i) t) = 1)).card ≤ 2 := by
  classical
  let S : Finset V :=
    (Finset.univ : Finset V).filter
      (fun i =>
        centreExponent (C i) t = n - 2 ∧
        positiveSupport (centreQuotient (C i) t) = 1)
  change S.card ≤ 2
  by_contra hcard
  have hthree : 2 < S.card := by omega
  obtain ⟨a, b, c, ha, hb, hc, hab, hac, hbc⟩ :=
    Finset.two_lt_card_iff.mp hthree
  have hA :
      centreExponent (C a) t = n - 2 ∧
        positiveSupport (centreQuotient (C a) t) = 1 :=
    (Finset.mem_filter.mp ha).2
  have hB :
      centreExponent (C b) t = n - 2 ∧
        positiveSupport (centreQuotient (C b) t) = 1 :=
    (Finset.mem_filter.mp hb).2
  have hC :
      centreExponent (C c) t = n - 2 ∧
        positiveSupport (centreQuotient (C c) t) = 1 :=
    (Finset.mem_filter.mp hc).2
  exact no_three_supportOne_secondLayer_of_four_le_n
    hp hcap hn4 hdelta0 hdeltaHalf ht hlam
    hab hac hbc (C a) (C b) (C c)
    hA.1 hB.1 hC.1 hA.2 hB.2 hC.2

namespace ProjectionOrdered

theorem projection_secondLayer_supportOne_card_le_two
    {V : Type*} [Fintype V]
    {p : V → Plane}
    (hp : Function.Injective p)
    {lam t delta : ℝ} {n : ℕ}
    (hcap : AngleCap p lam)
    (hn4 : 4 ≤ n)
    (hdelta0 : 0 ≤ delta)
    (hdeltaHalf : delta < (1 : ℝ) / 2)
    (ht : t = (n : ℝ) + delta)
    (hlam : lam = Real.pi / t)
    (C :
      letI : LinearOrder (ProjectionOrdered V) := projectionLinearOrder hp
      ∀ i : ProjectionOrdered V,
        CentreProjectiveCycle (reindexedPoint_injective hp) i) :
    letI : LinearOrder (ProjectionOrdered V) := projectionLinearOrder hp
    ((Finset.univ : Finset (ProjectionOrdered V)).filter
      (fun i =>
        centreExponent (C i) t = n - 2 ∧
        positiveSupport (centreQuotient (C i) t) = 1)).card ≤ 2 := by
  letI : LinearOrder (ProjectionOrdered V) := projectionLinearOrder hp
  have hcapRe : AngleCap (reindexedPoint p) lam :=
    angleCap_reindexedPoint hp hcap
  exact actual_secondLayer_supportOne_card_le_two
    (reindexedPoint_injective hp) hcapRe
    hn4 hdelta0 hdeltaHalf ht hlam C

end ProjectionOrdered

#print axioms actual_secondLayer_supportOne_card_le_two
#print axioms ProjectionOrdered.projection_secondLayer_supportOne_card_le_two

end JSP000404Research
