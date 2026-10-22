import JSP000404Research.SixPointSupportThreeMinimumDeletion
import JSP000404Research.SixPointExposedOrTwoHalfCapBridgesOrGain
import Mathlib.Tactic

/-!
# A six-vertex minimal counterexample has no free support-three exit

At n >= 5, the genuine 1+5 exponent profile has a top centre of exponent
n-1 and five original minima of exponent n-3. The existing exact-weight
deletion lemma proves that any nonmiddle support-three minimum admits a
non-top deletion which fully compensates the original six-point dyadic mass.

Consequently, if NO non-top deletion can compensate this mass, each
support-three minimum must either be strictly exposed or support
two vertex-disjoint sub-halfcap bridges with all eight cross-angles
strictly greater than lambda.

This is a genuine planar AngleCap theorem. It does not show that such a
configuration cannot occur, that the actual Boolean holes are available,
or that simultaneous sources can be paid without reuse.
-/

namespace JSP000404Research

theorem irreducible_six_point_support_three_exposed_or_two_halfcap_bridges
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane}
    (hp : Function.Injective p)
    {lam t delta : ℝ} {n : ℕ}
    (hcap : AngleCap p lam)
    (C : ∀ i : V, CentreProjectiveCycle hp i)
    (hcard : Fintype.card V = 6)
    (hn5 : 5 ≤ n)
    (hdelta0 : 0 ≤ delta)
    (hdeltaHalf : delta < (1 : ℝ) / 2)
    (ht : t = (n : ℝ) + delta)
    (hlam : lam = Real.pi / t)
    (top : V)
    (hTop : centreExponent (C top) t = n - 1)
    (hMin : ∀ v : V, v ≠ top →
      centreExponent (C v) t = n - 3)
    (hNoCompensatedDeletion :
      ∀ deleted : V, deleted ≠ top →
        ¬ (2 ^ (n - 1) + 5 * 2 ^ (n - 3) ≤
          ∑ v ∈ (Finset.univ.erase deleted : Finset V),
            2 ^ exponentAfterDeleteAt C
              (by rw [hcard]; omega) deleted t v))
    {i : V}
    (hit : i ≠ top)
    (hsupport : positiveSupport (centreQuotient (C i) t) = 3) :
    StrictlyExposedAt p i ∨
      TwoSeparatedHalfCapBridges (p := p) top i lam := by
  rcases six_point_support_three_middle_or_compensated_minimum_deletion
      hp hcap C hcard hn5 hdelta0 hdeltaHalf
      ht hlam top hTop hMin hit hsupport with
    hmiddle | ⟨deleted, hnotTop, hcomp⟩
  · by_cases hstrict : StrictlyExposedAt p i
    · exact Or.inl hstrict
    · right
      exact nonexposed_middle_hidden_two_disjoint_halfcap_bridges
        hp hcap (C i) hcard (by omega : 4 ≤ n)
        hdelta0 hdeltaHalf ht hlam
        hit (hMin i hit) hsupport hmiddle hstrict
  · exact False.elim (hNoCompensatedDeletion deleted hnotTop hcomp)

#print axioms irreducible_six_point_support_three_exposed_or_two_halfcap_bridges

end JSP000404Research
