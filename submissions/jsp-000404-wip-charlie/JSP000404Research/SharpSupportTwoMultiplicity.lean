import JSP000404Research.SharpPinnedSupportTwoCluster
import JSP000404Research.GeneralSupportTwoMultiplicity
import Mathlib.Tactic

/-!
# No two support-two deficit-two companions around one sharp centre

SharpPinnedSupportTwoCluster proves that every deficit-two/support-two centre i
around a sharp centre s satisfies OuterSmallAwayFrom(s,i).

Therefore two such centres a,b, together with any fourth point c, make triangle
a-b-c have two angles at most delta*lambda.  The global Sendov cap bounds the
third by pi-lambda, contradicting delta<1/2.

Unlike the earlier Fin 4 terminal, this theorem is valid in an arbitrary
finite ambient configuration.  The fourth point is supplied explicitly here;
a finite-cardinality corollary can choose it automatically when at least four
centres are present.
-/

namespace JSP000404Research

open Real

theorem no_two_supportTwo_deficitTwo_around_sharp
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane}
    (hp : Function.Injective p)
    (hcap : AngleCap p lam)
    {lam t delta : ℝ} {n : ℕ}
    (hn : 3 ≤ n)
    (hdelta0 : 0 ≤ delta)
    (hdeltaHalf : delta < (1 : ℝ) / 2)
    (ht : t = (n : ℝ) + delta)
    (hlam : lam = Real.pi / t)
    {s a b c : V}
    (hsa : s ≠ a) (hsb : s ≠ b) (hsc : s ≠ c)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hs : SharpAt p delta lam s)
    (Ca : CentreProjectiveCycle hp a)
    (Cb : CentreProjectiveCycle hp b)
    (hA : centreExponent Ca t = n - 2)
    (hB : centreExponent Cb t = n - 2)
    (hsupA :
      positiveSupport (centreQuotient Ca t) = 2)
    (hsupB :
      positiveSupport (centreQuotient Cb t) = 2) :
    False := by
  have htpos :
      0 < t :=
    sendov_scale_pos (by omega : 1 ≤ n) hdelta0 ht
  have hlampos : 0 < lam := by
    rw [hlam]
    exact div_pos Real.pi_pos htpos
  have ha :
      OuterSmallAwayFrom p delta lam s a :=
    supportTwo_outerSmallAwayFrom_sharp
      hp hcap hn hdelta0 hdeltaHalf ht hlam
      hsa hs Ca hA hsupA
  have hb :
      OuterSmallAwayFrom p delta lam s b :=
    supportTwo_outerSmallAwayFrom_sharp
      hp hcap hn hdelta0 hdeltaHalf ht hlam
      hsb hs Cb hB hsupB
  exact two_outerSmallAwayFrom_no_fourth
    hp hcap hdeltaHalf hlampos
    hsa hsb hsc hab hac hbc ha hb

#print axioms no_two_supportTwo_deficitTwo_around_sharp

end JSP000404Research
