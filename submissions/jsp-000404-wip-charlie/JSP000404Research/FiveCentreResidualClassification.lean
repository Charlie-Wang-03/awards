import JSP000404Research.FiveCentreStrictExposure
import JSP000404Research.SupportThreeTransitionDichotomy
import JSP000404Research.ConcreteDeficitThree
import Mathlib.Tactic

/-!
# General fifth-centre residual classification

Assume one top exponent (n-1) centre, one (n-3)/support-one
centre, and two further distinct centres whose quotient supports
are at most two, with NO exponent restriction on either companion.

For ANY fifth centre:
* its quotient support is at least three;
* its exponent is at most n-3;
* it is not strictly exposed;
* if it actually belongs to the n-3 layer, then its support is
  exactly three and every positive gap is a sign transition.

This improves the third-layer fifth-centre theorem by removing
BOTH n-3 exponent assumptions on the two companion centres.
These conclusions do not imply the original global dyadic capacity.
-/

namespace JSP000404Research

theorem fifth_general_residual_profile_of_top_third_saturation
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane}
    (hp : Function.Injective p)
    {lam t delta : ℝ} {n : ℕ}
    (hcap : AngleCap p lam)
    (hn : 4 ≤ n)
    (hdelta0 : 0 ≤ delta)
    (hdeltaHalf : delta < (1 : ℝ) / 2)
    (ht : t = (n : ℝ) + delta)
    (hlam : lam = Real.pi / t)
    {s a b c d : V}
    (hsa : s ≠ a) (hsb : s ≠ b) (hsc : s ≠ c) (hsd : s ≠ d)
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d)
    (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d)
    (Cs : CentreProjectiveCycle hp s)
    (Ca : CentreProjectiveCycle hp a)
    (Cb : CentreProjectiveCycle hp b)
    (Cc : CentreProjectiveCycle hp c)
    (Cd : CentreProjectiveCycle hp d)
    (hS : centreExponent Cs t = n - 1)
    (hA : centreExponent Ca t = n - 3)
    (hsupA : positiveSupport (centreQuotient Ca t) = 1)
    (hsupB : positiveSupport (centreQuotient Cb t) ≤ 2)
    (hsupC : positiveSupport (centreQuotient Cc t) ≤ 2) :
    3 ≤ positiveSupport (centreQuotient Cd t) ∧
    centreExponent Cd t ≤ n - 3 ∧
    ¬ StrictlyExposedAt p d ∧
    (centreExponent Cd t = n - 3 →
      positiveSupport (centreQuotient Cd t) = 3 ∧
      ∃ first : OtherVertex d,
        ∃ rest : List (OtherVertex d),
          Cd.rays = first :: rest ∧
          boolTransitionCountFrom
            (raySignAt hp d first)
            (liftedCentreSignPath hp d first rest) = 3) := by
  have hlow :
      3 ≤ positiveSupport (centreQuotient Cd t) :=
    fifth_support_ge_three_of_top_third_saturation
      hp hcap hn hdelta0 hdeltaHalf ht hlam
      hsa hsb hsc hsd hab hac had hbc hbd hcd
      Cs Ca Cb Cc Cd hS hA hsupA hsupB hsupC
  have hk :
      centreExponent Cd t ≤ n - 3 :=
    fifth_exponent_le_n_sub_three_of_top_third_saturation
      hp hcap hn hdelta0 hdeltaHalf ht hlam
      hsa hsb hsc hsd hab hac had hbc hbd hcd
      Cs Ca Cb Cc Cd hS hA hsupA hsupB hsupC
  have hnot : ¬ StrictlyExposedAt p d := by
    intro he
    exact no_fifth_strictlyExposed_of_top_third_one_two_low_support
      hp hcap hn hdelta0 hdeltaHalf ht hlam
      hsa hsb hsc hsd hab hac had hbc hbd hcd
      Cs Ca Cb Cc hS hA hsupA hsupB hsupC he
  refine ⟨hlow, hk, hnot, ?_⟩
  intro hD
  have hdelta1 : delta < 1 := by linarith
  have hDthree :
      positiveSupport (centreQuotient Cd t) = 3 := by
    rcases concrete_deficit_three_structure
      Cd hn hdelta0 hdelta1 ht hD with h1 | h2 | h3
    · omega
    · omega
    · exact h3.1
  have htpos :=
    sendov_scale_pos (by omega : 1 ≤ n) hdelta0 ht
  have htone :=
    sendov_scale_one_le (by omega : 1 ≤ n) hdelta0 ht
  exact ⟨hDthree,
    three_transitions_of_support_three_not_strictlyExposed
      hp hcap htpos htone hlam d Cd hDthree hnot⟩

#print axioms fifth_general_residual_profile_of_top_third_saturation

end JSP000404Research
