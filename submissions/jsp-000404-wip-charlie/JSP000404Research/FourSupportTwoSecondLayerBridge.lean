import JSP000404Research.ProjectionQTTTSmallPair
import JSP000404Research.FourSupportTwoDerangement
import Mathlib.Tactic

/-!
# Second-layer support-two bridge to the checked nine-state terminal

This is the only layer that connects the projective-cycle support-two geometry
to the dependency-light four-centre derangement theorem.

Keeping it separate makes the proof frontier explicit:
the finite four-centre logic is checked independently, while this file depends
on the heavier theorem that each support-two second-layer centre supplies a
local delta*lambda-small pair.
-/

namespace JSP000404Research

theorem four_supportTwo_secondLayer_reduce_to_derangement_nine
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane}
    {lam t delta : ℝ} {n : ℕ}
    (hp : Function.Injective p)
    (hcap : AngleCap p lam)
    (hn3 : 3 ≤ n)
    (hdelta0 : 0 ≤ delta)
    (hdeltaHalf : delta < (1 : ℝ) / 2)
    (ht : t = (n : ℝ) + delta)
    (hlam : lam = Real.pi / t)
    (C : ∀ v : V, CentreProjectiveCycle hp v)
    {a b c d : V}
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d)
    (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d)
    (haSecond : centreExponent (C a) t = n - 2)
    (hbSecond : centreExponent (C b) t = n - 2)
    (hcSecond : centreExponent (C c) t = n - 2)
    (hdSecond : centreExponent (C d) t = n - 2)
    (haSupport : positiveSupport (centreQuotient (C a) t) = 2)
    (hbSupport : positiveSupport (centreQuotient (C b) t) = 2)
    (hcSupport : positiveSupport (centreQuotient (C c) t) = 2)
    (hdSupport : positiveSupport (centreQuotient (C d) t) = 2) :
    FourSupportTwoDerangementPattern9 p delta lam a b c d := by
  have haSmall :=
    secondLayer_supportTwo_first_has_small_pair_among_three
      hp hcap hn3 hdelta0 hdeltaHalf ht hlam
      hab hac had hbc hbd hcd
      (C a) haSecond haSupport
  have hbSmall :=
    secondLayer_supportTwo_first_has_small_pair_among_three
      hp hcap hn3 hdelta0 hdeltaHalf ht hlam
      hab.symm hbc hbd hac had hcd
      (C b) hbSecond hbSupport
  have hcSmall :=
    secondLayer_supportTwo_first_has_small_pair_among_three
      hp hcap hn3 hdelta0 hdeltaHalf ht hlam
      hac.symm hbc.symm hcd hab had hbd
      (C c) hcSecond hcSupport
  have hdSmall :=
    secondLayer_supportTwo_first_has_small_pair_among_three
      hp hcap hn3 hdelta0 hdeltaHalf ht hlam
      had.symm hbd.symm hcd.symm hab hac hbc
      (C d) hdSecond hdSupport
  have htpos :
      0 < t :=
    sendov_scale_pos (by omega : 1 ≤ n) hdelta0 ht
  have hlampos : 0 < lam := by
    rw [hlam]
    exact div_pos Real.pi_pos htpos
  exact four_smallPairAmongOtherThree_reduce_to_derangement_nine
    hp hcap hdeltaHalf hlampos
    hab hac had hbc hbd hcd
    haSmall hbSmall hcSmall hdSmall

#print axioms four_supportTwo_secondLayer_reduce_to_derangement_nine

end JSP000404Research
