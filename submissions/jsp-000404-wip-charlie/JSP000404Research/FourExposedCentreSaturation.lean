import JSP000404Research.FiveCentreStrictExposure
import JSP000404Research.TopExponentSupportOneTransition
import Mathlib.Tactic

/-!
# Exactly four strictly exposed centres in the top/third-layer saturated configuration

Let s have exponent n-1, let a have exponent n-3 and support one,
and let b,c be two other centres with quotient support at most two.
All four are strictly exposed by the one-transition interval geometry.

The improved fifth-centre theorem excludes ANY other strictly exposed
point, independently of its exponent or quotient support. Thus the
globally strictly exposed vertices of the entire finite planar point
set are EXACTLY {s,a,b,c}.

This is a genuinely global geometric classification, but its
four-centre saturation hypotheses have not been derived for every
configuration relevant to the full JSP-000404 dyadic conjecture.
-/

namespace JSP000404Research

theorem strictlyExposedAt_iff_one_of_four_saturated_centres
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
    {s a b c : V}
    (hsa : s ≠ a) (hsb : s ≠ b) (hsc : s ≠ c)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (Cs : CentreProjectiveCycle hp s)
    (Ca : CentreProjectiveCycle hp a)
    (Cb : CentreProjectiveCycle hp b)
    (Cc : CentreProjectiveCycle hp c)
    (hS : centreExponent Cs t = n - 1)
    (hA : centreExponent Ca t = n - 3)
    (hsupA : positiveSupport (centreQuotient Ca t) = 1)
    (hsupB : positiveSupport (centreQuotient Cb t) ≤ 2)
    (hsupC : positiveSupport (centreQuotient Cc t) ≤ 2)
    (d : V) :
    StrictlyExposedAt p d ↔ d = s ∨ d = a ∨ d = b ∨ d = c := by
  have hdelta1 : delta < 1 := by linarith
  have htpos :=
    sendov_scale_pos (by omega : 1 ≤ n) hdelta0 ht
  have htone :=
    sendov_scale_one_le (by omega : 1 ≤ n) hdelta0 ht
  have hsupS :
      positiveSupport (centreQuotient Cs t) = 1 :=
    top_exponent_positiveSupport_eq_one Cs
      (by omega : 2 ≤ n) hdelta0 hdelta1 ht hS
  have hExS : StrictlyExposedAt p s :=
    strictlyExposedAt_of_positiveSupport_le_two
      hp hcap htpos htone hlam s Cs (by omega)
  have hExA : StrictlyExposedAt p a :=
    strictlyExposedAt_of_positiveSupport_le_two
      hp hcap htpos htone hlam a Ca (by omega)
  have hExB : StrictlyExposedAt p b :=
    strictlyExposedAt_of_positiveSupport_le_two
      hp hcap htpos htone hlam b Cb hsupB
  have hExC : StrictlyExposedAt p c :=
    strictlyExposedAt_of_positiveSupport_le_two
      hp hcap htpos htone hlam c Cc hsupC
  constructor
  · intro hExD
    by_cases hds : d = s
    · exact Or.inl hds
    by_cases hda : d = a
    · exact Or.inr (Or.inl hda)
    by_cases hdb : d = b
    · exact Or.inr (Or.inr (Or.inl hdb))
    by_cases hdc : d = c
    · exact Or.inr (Or.inr (Or.inr hdc))
    · have hcontra :=
        no_fifth_strictlyExposed_of_top_third_one_two_low_support
          hp hcap hn hdelta0 hdeltaHalf ht hlam
          hsa hsb hsc hds.symm
          hab hac hda.symm hbc hdb.symm hdc.symm
          Cs Ca Cb Cc hS hA hsupA hsupB hsupC hExD
      exact False.elim hcontra
  · intro hcase
    rcases hcase with hds | hda | hdb | hdc
    · rw [hds]; exact hExS
    · rw [hda]; exact hExA
    · rw [hdb]; exact hExB
    · rw [hdc]; exact hExC

#print axioms strictlyExposedAt_iff_one_of_four_saturated_centres

end JSP000404Research
