import JSP000404Research.CanonicalMarkedSideSemantics
import JSP000404Research.CanonicalSignGap
import JSP000404Research.CentreSignPath
import Mathlib.Tactic

/-!
# Canonical side semantics of zero quotient gaps

For an ordinary theta-ordered adjacent ray pair, quotient zero forbids a
canonical sign change, hence the two endpoints lie on the same side of the
centre in canonical planar order.

For the cyclic wrap gap, quotient zero forces the last raw sign to equal the
negation of the first raw sign.  Thus the two endpoints lie on opposite
canonical sides of the centre.
-/

namespace JSP000404Research

theorem ordinary_zero_quotient_canonicalSameSide
    {V : Type*} {p : V → Plane}
    (hp : Function.Injective p)
    (hcap : AngleCap p lam)
    {lam t : ℝ}
    (ht : 0 < t)
    (hlam : lam = Real.pi / t)
    (i : V)
    {j k : OtherVertex i}
    (hjk : j ≠ k)
    (horder :
      rayThetaAt hp i j ≤ rayThetaAt hp i k)
    (hq0 :
      Nat.floor
        (t * ((rayThetaAt hp i k -
          rayThetaAt hp i j) / Real.pi)) = 0) :
    CanonicalSameSide p i j.1 k.1 := by
  have hsign :
      raySignAt hp i j = raySignAt hp i k := by
    by_contra hne
    exact
      (floor_t_mul_gap_ne_zero_of_canonical_sign_ne
        hp hcap ht hlam i hjk horder hne) hq0
  exact
    (raySign_eq_iff_canonicalSameSide
      hp j.2 k.2).1 hsign

theorem wrap_zero_quotient_canonicalOppositeSides
    {V : Type*} {p : V → Plane}
    (hp : Function.Injective p)
    (hcap : AngleCap p lam)
    {lam t : ℝ}
    (ht : 0 < t)
    (hlam : lam = Real.pi / t)
    (i : V)
    {first last : OtherVertex i}
    (hfl : first ≠ last)
    (horder :
      rayThetaAt hp i first ≤ rayThetaAt hp i last)
    (hq0 :
      wrapRayQuotient hp i t first last = 0) :
    CanonicalOppositeSides p i last.1 first.1 := by
  have hsign :
      raySignAt hp i last =
        !raySignAt hp i first := by
    by_contra hne
    have hnonzero :=
      floor_t_mul_wrap_gap_ne_zero_of_canonical_sign_ne
        hp hcap ht hlam i hfl horder hne
    exact hnonzero (by
      simpa [wrapRayQuotient] using hq0)
  exact
    (raySign_not_eq_iff_canonicalOppositeSides
      hp last.2 first.2).1 hsign

#print axioms ordinary_zero_quotient_canonicalSameSide
#print axioms wrap_zero_quotient_canonicalOppositeSides

end JSP000404Research
