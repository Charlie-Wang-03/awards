import JSP000404Research.SixPointSupportThreeShape
import Mathlib.Tactic

/-!
# Unconditional six-point pinned support-three middle/outlet dichotomy

The existing support-three terminal has exactly three possible locations
for its unique hidden positive quotient. Rather than postulating the
non-middle hypothesis, this theorem exposes the middle shape as the
single explicit alternative to an actual non-top positive-positive
cyclic ray position. The middle case is not excluded here.

This is an actual AngleCap wrapper, NOT a proof of the full lower branch.
-/

namespace JSP000404Research

/-- An unconditional shape split for the actual six-centre configuration:
either the middle quotient is the unique hidden positive entry, or an
endpoint hidden positive entry creates a non-top positive-positive outlet. -/
theorem six_point_support_three_middle_or_end_outlet
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane}
    (hp : Function.Injective p)
    {lam t delta : ℝ} {n : ℕ}
    (hcap : AngleCap p lam)
    (hcard : Fintype.card V = 6)
    (hn : 4 ≤ n)
    (hdelta0 : 0 ≤ delta)
    (hdeltaHalf : delta < (1 : ℝ) / 2)
    (ht : t = (n : ℝ) + delta)
    (hlam : lam = Real.pi / t)
    {s i : V}
    (hsi : s ≠ i)
    (hs : SharpAt p delta lam s)
    (C : CentreProjectiveCycle hp i)
    (hexp : centreExponent C t = n - 3)
    (hsupport : positiveSupport (centreQuotient C t) = 3) :
    ∃ first0 : OtherVertex i,
    ∃ rest0 : List (OtherVertex i),
    ∃ k : ℕ,
    ∃ r : OtherVertex i,
    ∃ rest : List (OtherVertex i),
    ∃ qFirst qLast qHidden : ℕ,
    ∃ qmid : List ℕ,
      C.rays = first0 :: rest0 ∧
      C.rays.rotate k =
        (⟨s,hsi⟩ : OtherVertex i) :: r :: rest ∧
      (quotientList t C.gaps).rotate k =
        qFirst :: qmid ++ [qLast] ∧
      qHidden ≠ 0 ∧
      (qmid = [0,qHidden,0] ∨
        ((qmid = [qHidden,0,0] ∧
            1 ≤ qFirst ∧ 1 ≤ qHidden) ∨
         (qmid = [0,0,qHidden] ∧
            1 ≤ qHidden ∧ 1 ≤ qLast))) := by
  obtain ⟨first0, rest0, k, r, rest,
      qFirst, qLast, qHidden, qmid,
      hrays, hrot, hq, hFirst, hLast, _hmidLen,
      hHidden, hshape⟩ :=
    exists_six_point_sharp_pinned_support_three_shape
      hp hcap hcard hn hdelta0 hdeltaHalf ht hlam
      hsi hs C hexp hsupport
  have hH : 1 ≤ qHidden :=
    Nat.one_le_iff_ne_zero.mpr hHidden
  refine ⟨first0, rest0, k, r, rest,
    qFirst, qLast, qHidden, qmid,
    hrays, hrot, hq, hHidden, ?_⟩
  rcases hshape with hleft | hmid | hright
  · exact Or.inr (Or.inl ⟨hleft, hFirst, hH⟩)
  · exact Or.inl hmid
  · exact Or.inr (Or.inr ⟨hright, hH, hLast⟩)

#print axioms six_point_support_three_middle_or_end_outlet

end JSP000404Research
