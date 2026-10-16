import JSP000404Research.FourPointConvexSeparation
import JSP000404Research.FourCentreMixedExteriorOutlet
import JSP000404Research.ExposedSupportIntervalFinFour
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

The first theorem is a quantitative necessary frontier. The second
combines it with the existing, separately proved exposed-support theorem
to EXCLUDE the exterior branch under actual AngleCap and transition costs.
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

/-- Under genuine four-point AngleCap, a mixed three-centre family of
transition cost 2*n forces the fourth vertex into their convex hull.
No unproved geometric implication is assumed: the needed long support
interval is furnished by ExposedSupportIntervalFinFour. -/
theorem mixed_four_fourth_mem_triangle_of_transition_cost
    {p : Fin 4 → Plane}
    (hp : Function.Injective p)
    {t delta lam : ℝ} {n : ℕ}
    (hcap : AngleCap p lam)
    {s a b c : Fin 4}
    (hsa : s ≠ a) (hsb : s ≠ b) (hsc : s ≠ c)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
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
    p c ∈ convexHull ℝ ({p s, p a, p b} : Set Plane) := by
  classical
  by_contra hout
  obtain ⟨hExpose, hShort⟩ :=
    mixed_four_exterior_strict_exposure_and_short_turn
      hp hsa hsb hsc hab hac hbc hout
      hn hdelta0 hdeltaHalf ht hlam Cs Ca Cb Hs Ha Hb hqsum
  have htpos : 0 < t :=
    sendov_scale_pos hn hdelta0 ht
  have htone : (1 : ℝ) ≤ t := by
    have hnR : (1 : ℝ) ≤ (n : ℝ) := by
      exact_mod_cast hn
    rw [ht]
    linarith
  have hother : Nonempty (OtherVertex c) :=
    ⟨⟨s, hsc⟩⟩
  let Cc : CentreProjectiveCycle hp c :=
    Classical.choice (exists_centreProjectiveCycle hp c hother)
  obtain ⟨Sc, hLong⟩ :=
    exists_supportIntervalCertificate_of_strictlyExposed_fin_four
      hp hcap htpos htone hlam Cc hExpose
  exact (not_lt_of_ge hLong) (hShort Sc)

#print axioms mixed_four_exterior_strict_exposure_and_short_turn
#print axioms mixed_four_fourth_mem_triangle_of_transition_cost

end JSP000404Research
