import JSP000404Research.SixPointNFourNoCoverWithoutEquality
import JSP000404Research.TransitionSameSignDisjoint
import Mathlib.Tactic

/-!
# Actual ordinary-transition phase cover excluded in the n=4 six-point profile

The earlier conditional phase-cover theorem assumed separately that
same-sign unit-gap slots were unusable.  For the concrete, ordinary
adjacent sign-transition predicate, this follows from the independently
proved geometric/list-index disjointness theorem and is NOT an additional
assumption.

The quantitative phase-cover lower bound remains a hypothesis.  Neither
this theorem nor its dependencies construct a global six-source Boolean-hole
payment or settle the original JSP-000404 problem.
-/

namespace JSP000404Research

/-- Any genuinely phase-dependent obstruction predicate supported only at
ordinary transition slots is excluded by the quantitative cover inequality.
The same-sign-unusable premise of the earlier theorem is proved rather than
assumed, and phase dependence is preserved. -/
theorem six_point_n_four_no_transition_supported_phase_cover
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane}
    (hp : Function.Injective p)
    {lam t delta : ℝ}
    (hcap : AngleCap p lam)
    (hdelta0 : 0 ≤ delta)
    (hdeltaHalf : delta < (1 : ℝ) / 2)
    (ht : t = (4 : ℝ) + delta)
    (hlam : lam = Real.pi / t)
    (C : ∀ i : V, CentreProjectiveCycle hp i)
    (hcard : Fintype.card V = 6)
    (top : V)
    (hTop : centreExponent (C top) t = 3)
    (hMin : ∀ i : V, i ≠ top →
      centreExponent (C i) t = 1)
    (A : GlobalUnitGapSlot C t → ℝ → Prop)
    (S : Finset (GlobalUnitGapSlot C t))
    (hTransition :
      ∀ u : GlobalUnitGapSlot C t, ∀ x : ℝ,
        A u x → GlobalUnitGapOrdinaryTransition C t u)
    (hcoverLower :
      ∀ T : Finset (GlobalUnitGapSlot C t), T ⊆ S →
        PredicateCovers A T →
        (4 : ℝ) + delta ≤ (T.card : ℝ) * delta) :
    ¬ PredicateCovers A S := by
  apply six_point_n_four_no_transition_only_phase_cover_without_equality
    hp hcap hdelta0 hdeltaHalf ht hlam
    C hcard top hTop hMin A S
  · intro u hsame x hx
    exact (globalUnitGapSameSign_not_ordinaryTransition C t u hsame)
      (hTransition u x hx)
  · exact hcoverLower

/-- A genuine ordinary-transition-only phase cover is impossible when the
specific lower bound for such covers is available from geometry. -/
theorem six_point_n_four_no_ordinary_transition_phase_cover
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane}
    (hp : Function.Injective p)
    {lam t delta : ℝ}
    (hcap : AngleCap p lam)
    (hdelta0 : 0 ≤ delta)
    (hdeltaHalf : delta < (1 : ℝ) / 2)
    (ht : t = (4 : ℝ) + delta)
    (hlam : lam = Real.pi / t)
    (C : ∀ i : V, CentreProjectiveCycle hp i)
    (hcard : Fintype.card V = 6)
    (top : V)
    (hTop : centreExponent (C top) t = 3)
    (hMin : ∀ i : V, i ≠ top →
      centreExponent (C i) t = 1)
    (S : Finset (GlobalUnitGapSlot C t))
    (hcoverLower :
      ∀ T : Finset (GlobalUnitGapSlot C t), T ⊆ S →
        PredicateCovers
          (fun u (_ : ℝ) => GlobalUnitGapOrdinaryTransition C t u) T →
        (4 : ℝ) + delta ≤ (T.card : ℝ) * delta) :
    ¬ PredicateCovers
      (fun u (_ : ℝ) => GlobalUnitGapOrdinaryTransition C t u) S := by
  apply six_point_n_four_no_transition_supported_phase_cover
    hp hcap hdelta0 hdeltaHalf ht hlam
    C hcard top hTop hMin
    (fun u (_ : ℝ) => GlobalUnitGapOrdinaryTransition C t u) S
  · intro u x hx
    exact hx
  · exact hcoverLower

#print axioms six_point_n_four_no_transition_supported_phase_cover
#print axioms six_point_n_four_no_ordinary_transition_phase_cover

end JSP000404Research
