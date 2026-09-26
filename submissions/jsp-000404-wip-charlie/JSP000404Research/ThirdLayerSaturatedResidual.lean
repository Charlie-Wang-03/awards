import JSP000404Research.ThirdLayerNoFifthExposed
import JSP000404Research.SupportThreeTransitionDichotomy
import JSP000404Research.SupportLeTwoTransitionInterval
import JSP000404Research.ConcreteDeficitThree
import Mathlib.Tactic

/-!
# Saturated third-layer packing forces three-transition residual centres

Suppose a lower-branch configuration contains

* one top n-1 centre s,
* one n-3/support-one centre a,
* two n-3/support-two centres b,c.

ThirdLayerNoFifthExposed shows that any fifth distinct point d cannot be
strictly exposed.

If d is itself in the n-3 layer, ConcreteDeficitThree restricts its support to
1,2,3.  Support 1 or 2 is impossible because every support<=2 concrete centre
is strictly exposed.  Thus d has support three.

Finally SupportThreeTransitionDichotomy says a support-three centre is either
strictly exposed or has exactly three sign transitions.  The exposed branch is
already excluded, so d must use all three positive-gap transition slots.
-/

namespace JSP000404Research

theorem fifth_deficit_three_forced_support_three_three_transitions
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane}
    (hp : Function.Injective p)
    (hcap : AngleCap p lam)
    {lam t delta : ℝ} {n : ℕ}
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
    (hsupA :
      positiveSupport (centreQuotient Ca t) = 1)
    (hsupB :
      positiveSupport (centreQuotient Cb t) = 2)
    (hsupC :
      positiveSupport (centreQuotient Cc t) = 2) :
    positiveSupport (centreQuotient Cd t) = 3
      ∧
    ∃ first : OtherVertex d,
      ∃ rest : List (OtherVertex d),
        Cd.rays = first :: rest ∧
        boolTransitionCountFrom
            (raySignAt hp d first)
            (liftedCentreSignPath hp d first rest) = 3 := by
  have htpos :=
    sendov_scale_pos (by omega : 1 ≤ n) hdelta0 ht
  have htone :=
    sendov_scale_one_le (by omega : 1 ≤ n) hdelta0 ht
  have hnotExpose :
      ¬ StrictlyExposedAt p d := by
    intro hExpose
    exact
      no_fifth_strictlyExposed_of_top_supportOne_two_supportTwo_deficitThree
        hp hcap hn hdelta0 hdeltaHalf ht hlam
        hsa hsb hsc hsd
        hab hac had hbc hbd hcd
        Cs Ca Cb Cc
        hS hA hB hC
        hsupA hsupB hsupC
        hExpose

  have hdelta1 : delta < 1 := by linarith
  have hsupD :
      positiveSupport (centreQuotient Cd t) = 3 := by
    rcases concrete_deficit_three_structure
        Cd hn hdelta0 hdelta1 ht hD with h1 | h2 | h3
    · have hexposed :=
        strictlyExposedAt_of_positiveSupport_le_two
          hp hcap htpos htone hlam d Cd
          (by rw [h1.1]; omega)
      exact False.elim (hnotExpose hexposed)
    · have hexposed :=
        strictlyExposedAt_of_positiveSupport_le_two
          hp hcap htpos htone hlam d Cd
          (by rw [h2.1]; omega)
      exact False.elim (hnotExpose hexposed)
    · exact h3.1

  have hthree :=
    three_transitions_of_support_three_not_strictlyExposed
      hp hcap htpos htone hlam
      d Cd hsupD hnotExpose
  exact ⟨hsupD, hthree⟩

#print axioms fifth_deficit_three_forced_support_three_three_transitions

end JSP000404Research
