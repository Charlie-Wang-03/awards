import JSP000404Research.SixPointThirdLayerTerminal
import JSP000404Research.SixPointTopDeletionExceptionReduction
import Mathlib.Tactic

/-!
# Actual large minimum-layer overweight branch: top deletion or precise exceptions

This module stitches the exact six-point terminal classification to the
actual top-deletion compensation theorem. No separate six-point hypothesis
or separate five-minimum exponent profile is required in the input.

The remaining two low-support patterns are genuine original geometric
obligations; this does NOT resolve the universal all-source payment.
-/

namespace JSP000404Research

open scoped BigOperators

/-- In the large n-3 minimum layer, a unique sharp top forces the six-point
profile. Either deleting that exact top is itself overweight, or two
surviving minima have one of the two prescribed low-support profiles. -/
theorem large_minimum_top_deletion_overweight_or_low_support
    {V : Type*} [LinearOrder V] [Fintype V] [Nonempty V]
    {p : V → Plane} (hp : Function.Injective p)
    {lam t delta : ℝ} {n : ℕ}
    (hcap : AngleCap p lam)
    (hcard : 4 ≤ Fintype.card V)
    (hn : 5 ≤ n)
    (hdelta0 : 0 ≤ delta)
    (hdeltaHalf : delta < (1 : ℝ) / 2)
    (ht : t = (n : ℝ) + delta)
    (hlam : lam = Real.pi / t)
    (C : ∀ i : V, CentreProjectiveCycle hp i)
    (r0 top : V)
    (hminExp : centreExponent (C r0) t = n - 3)
    (hmin :
      ∀ i : V,
        centreExponent (C r0) t ≤
          centreExponent (C i) t)
    (hTop : centreExponent (C top) t = n - 1)
    (hover :
      2 ^ n < ∑ i : V, 2 ^ centreExponent (C i) t)
    (hchildR0 :
      deletionPostWeight
          (concreteDeletionAfter C (by omega) t) r0
        ≤ 2 ^ n)
    (hminCard :
      5 ≤
        (minimumExponentVertices
          (fun i => centreExponent (C i) t) r0).card) :
    (2 ^ n <
      ∑ v ∈ (Finset.univ.erase top : Finset V),
        2 ^ exponentAfterDeleteTopAt C
          (by omega : 3 ≤ Fintype.card V) top t v)
    ∨
    (∃ a b : V,
      a ≠ top ∧ b ≠ top ∧ a ≠ b ∧
      positiveSupport (centreQuotient (C a) t) = 1 ∧
      positiveSupport (centreQuotient (C b) t) = 2)
    ∨
    (∃ a b : V,
      a ≠ top ∧ b ≠ top ∧ a ≠ b ∧
      positiveSupport (centreQuotient (C a) t) = 2 ∧
      positiveSupport (centreQuotient (C b) t) = 2) := by
  classical
  have hprof := large_n_sub_three_minimum_with_top_forces_six_points
    hp hcap hcard (by omega : 4 ≤ n)
    hdelta0 hdeltaHalf ht hlam C r0 top
    hminExp hmin hTop hover hchildR0 hminCard
  have hcard6 : Fintype.card V = 6 := hprof.2.2
  have hNoSecond :
      ((Finset.univ : Finset V).filter
        (fun i => i ≠ top ∧
          centreExponent (C i) t = n - 2)) = ∅ :=
    Finset.card_eq_zero.mp hprof.2.1
  have hdelta1 : delta < (1 : ℝ) := by linarith
  have hTopUnique :
      ∀ i : V,
        centreExponent (C i) t = n - 1 → i = top := by
    intro i hi
    exact topExponent_eq_fixed_top
      hp hcap (by omega) (by omega)
      hdelta0 hdeltaHalf ht hlam C top i hTop hi
  have hMinFive :
      ∀ v : V, v ≠ top →
        centreExponent (C v) t = n - 3 := by
    intro v hvt
    have hlow : n - 3 ≤ centreExponent (C v) t := by
      rw [← hminExp]
      exact hmin v
    have hhigh : centreExponent (C v) t < n :=
      centreExponent_lt_n
        (C v) n delta t (by omega : 1 ≤ n)
        hdelta0 hdelta1 ht
    have hNotTop : centreExponent (C v) t ≠ n - 1 := by
      intro h
      exact hvt (hTopUnique v h)
    have hNotSecond :
        centreExponent (C v) t ≠ n - 2 := by
      intro h
      have hmem :
          v ∈ ((Finset.univ : Finset V).filter
            (fun i => i ≠ top ∧
              centreExponent (C i) t = n - 2)) := by
        simp [hvt, h]
      simpa [hNoSecond] using hmem
    omega
  exact six_point_top_deletion_overweight_or_low_support
    hp hcap C hn hdelta0 hdeltaHalf ht hlam
    hcard6 top hTop hMinFive

#print axioms large_minimum_top_deletion_overweight_or_low_support

end JSP000404Research
