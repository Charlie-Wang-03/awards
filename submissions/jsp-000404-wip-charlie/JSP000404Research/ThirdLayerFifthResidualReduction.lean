import JSP000404Research.ThirdLayerTransitionPacking
import JSP000404Research.ThirdLayerSaturatedResidual
import JSP000404Research.ConcreteDeficitThree
import Mathlib.Tactic

/-!
# Fifth-centre third-layer residual reduction without preset support-two equalities

Among a top n-1 centre, an n-3 support-one centre, and two n-3
centres whose supports are at most two, the latter two automatically
have support exactly two: a second support-one centre contradicts
four-centre transition-quotient packing, while support three is
excluded by assumption. The fifth n-3 centre must then have
support three and exactly three sign transitions.

This removes two equality hypotheses from the already certified
fifth-deficit-three classification. It does NOT pay the global
translated-loss / terminal-twin debt of the original JSP problem.
-/

namespace JSP000404Research

theorem fifth_deficit_three_forced_residual_of_two_small_supports
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
    (hB : centreExponent Cb t = n - 3)
    (hC : centreExponent Cc t = n - 3)
    (hD : centreExponent Cd t = n - 3)
    (hsupA : positiveSupport (centreQuotient Ca t) = 1)
    (hsupB : positiveSupport (centreQuotient Cb t) ≤ 2)
    (hsupC : positiveSupport (centreQuotient Cc t) ≤ 2) :
    positiveSupport (centreQuotient Cd t) = 3 ∧
      ∃ first : OtherVertex d,
        ∃ rest : List (OtherVertex d),
          Cd.rays = first :: rest ∧
            boolTransitionCountFrom
              (raySignAt hp d first)
              (liftedCentreSignPath hp d first rest) = 3 := by
  have hdelta1 : delta < 1 := by linarith
  have hB2 : positiveSupport (centreQuotient Cb t) = 2 := by
    rcases concrete_deficit_three_structure
        Cb hn hdelta0 hdelta1 ht hB with h1 | h2 | h3
    · have hcontra : False :=
        no_top_three_deficit_three_support_le_two_with_two_support_one
          hp hcap hn hdelta0 hdeltaHalf ht hlam
          hsa hsb hsc hab hac hbc
          Cs Ca Cb Cc hS hA hB hsupA h1.1 hsupC
      exact False.elim hcontra
    · exact h2.1
    · omega
  have hC2 : positiveSupport (centreQuotient Cc t) = 2 := by
    rcases concrete_deficit_three_structure
        Cc hn hdelta0 hdelta1 ht hC with h1 | h2 | h3
    · have hcontra : False :=
        no_top_three_deficit_three_support_le_two_with_two_support_one
          hp hcap hn hdelta0 hdeltaHalf ht hlam
          hsa hsc hsb hac hab hbc.symm
          Cs Ca Cc Cb hS hA hC hsupA h1.1 hsupB
      exact False.elim hcontra
    · exact h2.1
    · omega
  exact
    fifth_deficit_three_forced_support_three_three_transitions
      hp hcap hn hdelta0 hdeltaHalf ht hlam
      hsa hsb hsc hsd
      hab hac had hbc hbd hcd
      Cs Ca Cb Cc Cd
      hS hA hB hC hD
      hsupA hB2 hC2

#print axioms fifth_deficit_three_forced_residual_of_two_small_supports

end JSP000404Research
