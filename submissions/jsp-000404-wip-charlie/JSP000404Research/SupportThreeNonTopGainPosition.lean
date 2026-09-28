import JSP000404Research.SixPointSupportThreeShape
import Mathlib.Tactic

/-!
# Non-top positive-positive vertices in the six-point pinned support-three cycle

For a six-point n-3/support-three centre pinned at the sharp top, the quotient
cycle has the form

  qFirst :: qmid ++ [qLast],

with qFirst,qLast>0 and

  qmid = [qHidden,0,0]
       or [0,qHidden,0]
       or [0,0,qHidden],

where qHidden>0.

The first and third shapes contain a non-top ray flanked by two positive
quotients:

* [qHidden,0,0]: the first ray after the top is flanked by qFirst,qHidden;
* [0,0,qHidden]: the final ray before the top is flanked by qHidden,qLast.

Only the middle shape [0,qHidden,0] has the sharp top as the unique ray whose
two adjacent quotients are both positive.

This is the discrete deletion outlet needed before lifting to concrete
compensated deletion.
-/

namespace JSP000404Research

/-- Five-position pure list version. -/
theorem support_three_end_hidden_has_nonTop_flanked_positive
    (qFirst qLast qHidden : ℕ)
    (hFirst : 1 ≤ qFirst)
    (hLast : 1 ≤ qLast)
    (hHidden : qHidden ≠ 0)
    (qmid : List ℕ)
    (hshape :
      qmid = [qHidden,0,0] ∨
      qmid = [0,qHidden,0] ∨
      qmid = [0,0,qHidden])
    (hnotMiddle : qmid ≠ [0,qHidden,0]) :
    (qmid = [qHidden,0,0] ∧
      1 ≤ qFirst ∧ 1 ≤ qHidden)
      ∨
    (qmid = [0,0,qHidden] ∧
      1 ≤ qHidden ∧ 1 ≤ qLast) := by
  have hH : 1 ≤ qHidden := Nat.one_le_iff_ne_zero.mpr hHidden
  rcases hshape with hleft | hmid | hright
  · exact Or.inl ⟨hleft, hFirst, hH⟩
  · exact False.elim (hnotMiddle hmid)
  · exact Or.inr ⟨hright, hH, hLast⟩

/-- Geometric six-point wrapper retaining the actual pinned ray list.

If the hidden positive quotient is not in the middle-middle position, then
either the first non-top ray after the sharp top or the final non-top ray
before the sharp top is explicitly identified as a positive-positive cyclic
vertex.
-/
theorem six_point_support_three_nonMiddle_hidden_position
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane}
    (hp : Function.Injective p)
    (hcap : AngleCap p lam)
    {lam t delta : ℝ} {n : ℕ}
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
    (hsupport :
      positiveSupport (centreQuotient C t) = 3)
    (hNoMiddle :
      ∀ first0 rest0 k r rest qFirst qLast qHidden qmid,
        C.rays = first0 :: rest0 →
        C.rays.rotate k =
          (⟨s,hsi⟩ : OtherVertex i) :: r :: rest →
        (quotientList t C.gaps).rotate k =
          qFirst :: qmid ++ [qLast] →
        1 ≤ qFirst →
        1 ≤ qLast →
        qmid.length = 3 →
        qHidden ≠ 0 →
        (qmid = [qHidden,0,0] ∨
         qmid = [0,qHidden,0] ∨
         qmid = [0,0,qHidden]) →
        qmid ≠ [0,qHidden,0]) :
    ∃ first0 rest0 k r rest qFirst qLast qHidden qmid,
      C.rays = first0 :: rest0 ∧
      C.rays.rotate k =
        (⟨s,hsi⟩ : OtherVertex i) :: r :: rest ∧
      (quotientList t C.gaps).rotate k =
        qFirst :: qmid ++ [qLast] ∧
      qHidden ≠ 0 ∧
      (
        (qmid = [qHidden,0,0] ∧
          1 ≤ qFirst ∧ 1 ≤ qHidden)
        ∨
        (qmid = [0,0,qHidden] ∧
          1 ≤ qHidden ∧ 1 ≤ qLast)
      ) := by
  obtain ⟨first0,rest0,k,r,rest,
      qFirst,qLast,qHidden,qmid,
      hrays,hrot,hq,hFirst,hLast,hmidLen,
      hHidden,hshape⟩ :=
    exists_six_point_sharp_pinned_support_three_shape
      hp hcap hcard hn hdelta0 hdeltaHalf ht hlam
      hsi hs C hexp hsupport
  have hnotMid :
      qmid ≠ [0,qHidden,0] :=
    hNoMiddle first0 rest0 k r rest
      qFirst qLast qHidden qmid
      hrays hrot hq hFirst hLast hmidLen
      hHidden hshape
  have hend :=
    support_three_end_hidden_has_nonTop_flanked_positive
      qFirst qLast qHidden hFirst hLast hHidden
      qmid hshape hnotMid
  exact ⟨first0,rest0,k,r,rest,
    qFirst,qLast,qHidden,qmid,
    hrays,hrot,hq,hHidden,hend⟩

#print axioms support_three_end_hidden_has_nonTop_flanked_positive
#print axioms six_point_support_three_nonMiddle_hidden_position

end JSP000404Research
