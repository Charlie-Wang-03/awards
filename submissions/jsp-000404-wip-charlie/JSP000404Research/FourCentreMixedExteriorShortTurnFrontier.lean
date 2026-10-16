import JSP000404Research.FourPointConvexSeparation
import JSP000404Research.FourCentreMixedExteriorOutlet
import Mathlib.Tactic

/-!
# Mixed four-centre exterior obstruction: strict exposure, short support arcs

Combine the actual four-point convex-separation theorem with the certified
mixed-exterior dual-turn packing contradiction.

Given three transition certificates of total cost 2*n, if the fourth
point lies outside the triangle of those three, it is strictly exposed.
Moreover EVERY genuine SupportIntervalCertificate at the fourth point
has turnLength < lam: a certificate of length >= lam would exceed the
2*pi total dual-turn budget when delta < 1/2.

This is a necessary geometric frontier, not the missing theorem that
strict exposure automatically supplies a long support certificate.
The latter implication is NOT assumed or claimed.
-/

namespace JSP000404Research

theorem mixed_four_exterior_strict_exposure_and_short_turn
    {p : Fin 4 → Plane}
    (hp : Function.Injective p)
    {s a b c : Fin 4}
    (hsa : s ≠ a) (hsb : s ≠ b) (hsc : s ≠ c)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hout : p c ∉ convexHull ℝ
      ({p s, p a, p b} : Set Plane))
    {t delta lam : ℝ} {n : ℕ}
    (hn : 1 ≤ n)
    (hdelta0 : 0 ≤ delta)
    (hdeltaHalf : delta < (1 : ℝ) / 2)
    (ht : t = (n : ℝ) + delta)
    (hlam : lam = Real.pi / t)
    (Cs : CentreProjectiveCycle hp s)
    (Ca : CentreProjectiveCycle hp a)
    (Cb : CentreProjectiveCycle hp b)
    (Hs : HighExponentTransitionIntervalCertificate hp t s Cs)
    (Ha : HighExponentTransitionIntervalCertificate hp t a Ca)
    (Hb : HighExponentTransitionIntervalCertificate hp t b Cb)
    (hqsum : Hs.qe + Ha.qe + Hb.qe = 2 * n) :
    StrictlyExposedAt p c ∧
      ∀ (Cc : SupportIntervalCertificate (p := p) c),
        Cc.turnLength < lam := by
  constructor
  · exact strictlyExposedAt_of_not_mem_other_triangle_fin_four
      hp hsa hsb hsc hab hac hbc hout
  · intro Cc
    by_contra hshort
    have hlong : lam ≤ Cc.turnLength :=
      le_of_not_gt hshort
    exact no_mixed_fourth_support_arc_of_one_cap_unit
      hsa hsb hsc hab hac hbc
      hn hdelta0 hdeltaHalf ht hlam
      Cs Ca Cb Hs Ha Hb hqsum Cc hlong

#print axioms mixed_four_exterior_strict_exposure_and_short_turn

end JSP000404Research
