import JSP000404Research.GeneralZeroGapActualAngle
import JSP000404Research.SharpOuterAngles
import Mathlib.Tactic

/-!
# Arbitrary-cardinality support-two zero gaps avoid a sharp ray

The Fin 4 theorem SharpAvoidsZeroGap used uniqueness of the zero gap only after
proving a local fact: a quotient-zero gap is delta-small and therefore cannot
touch the ray to a sharp centre.

GeneralZeroGapActualAngle now supplies the same local delta-small estimate for
arbitrary centre size.  Hence the avoidance statement itself has no Fin 4
dependence.

Both ordinary displayed gaps and the final wrap gap are covered here.
-/

namespace JSP000404Research

open Real

theorem displayed_ordinary_zero_gap_endpoints_ne_sharp
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane}
    (hp : Function.Injective p)
    (hcap : AngleCap p lam)
    {lam t delta : ℝ} {n : ℕ}
    (hn : 3 ≤ n)
    (hdelta0 : 0 ≤ delta)
    (hdeltaHalf : delta < (1 : ℝ) / 2)
    (ht : t = (n : ℝ) + delta)
    (hlam : lam = Real.pi / t)
    {s i : V}
    (hsi : s ≠ i)
    (hs : SharpAt p delta lam s)
    (C : CentreProjectiveCycle hp i)
    (hexp : centreExponent C t = n - 2)
    (hsupport :
      positiveSupport (centreQuotient C t) = 2)
    (first right : OtherVertex i)
    (before tail : List (OtherVertex i))
    (hrays :
      C.rays = first :: (before ++ right :: tail))
    (qpre qpost : List ℕ)
    (hq :
      quotientList t C.gaps = qpre ++ 0 :: qpost)
    (hlen : qpre.length = before.length)
    (hneq :
      (first :: before).getLast (by simp) ≠ right) :
    ((first :: before).getLast (by simp)).1 ≠ s ∧
      right.1 ≠ s := by
  have hdelta1 : delta < 1 := by linarith
  have htpos :
      0 < t :=
    sendov_scale_pos (by omega : 1 ≤ n) hdelta0 ht
  have hlampos : 0 < lam := by
    rw [hlam]
    exact div_pos Real.pi_pos htpos
  have hsmall :=
    displayed_ordinary_zero_gap_actual_angle_le_delta_lam
      hp hcap hn hdelta0 hdelta1 ht hlam
      i C hexp hsupport first right before tail
      hrays qpre qpost hq hlen hneq
  let left : OtherVertex i :=
    (first :: before).getLast (by simp)
  constructor
  · intro hleftS
    have hsRight : s ≠ right.1 := by
      intro hsr
      apply hneq
      apply Subtype.ext
      calc
        left.1 = s := hleftS
        _ = right.1 := hsr
    have hlower :=
      delta_mul_lam_lt_outer_angle_of_sharp
        hp hcap hdeltaHalf hlampos
        hsi hsRight right.2.symm hs
    have hsmall' :
        EuclideanGeometry.angle (p s) (p i) (p right.1) ≤
          delta * lam := by
      simpa [left, hleftS] using hsmall
    linarith
  · intro hrightS
    have hsLeft : s ≠ left.1 := by
      intro hsl
      apply hneq
      apply Subtype.ext
      calc
        left.1 = s := hsl.symm
        _ = right.1 := hrightS.symm
    have hlower :=
      delta_mul_lam_lt_outer_angle_of_sharp
        hp hcap hdeltaHalf hlampos
        hsi hsLeft left.2.symm hs
    have hsmall' :
        EuclideanGeometry.angle (p s) (p i) (p left.1) ≤
          delta * lam := by
      rw [EuclideanGeometry.angle_comm]
      simpa [left, hrightS] using hsmall
    linarith

theorem displayed_wrap_zero_gap_endpoints_ne_sharp
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane}
    (hp : Function.Injective p)
    (hcap : AngleCap p lam)
    {lam t delta : ℝ} {n : ℕ}
    (hn : 3 ≤ n)
    (hdelta0 : 0 ≤ delta)
    (hdeltaHalf : delta < (1 : ℝ) / 2)
    (ht : t = (n : ℝ) + delta)
    (hlam : lam = Real.pi / t)
    {s i : V}
    (hsi : s ≠ i)
    (hs : SharpAt p delta lam s)
    (C : CentreProjectiveCycle hp i)
    (hexp : centreExponent C t = n - 2)
    (hsupport :
      positiveSupport (centreQuotient C t) = 2)
    (first : OtherVertex i)
    (rest : List (OtherVertex i))
    (hrays : C.rays = first :: rest)
    (qpre : List ℕ)
    (hq :
      quotientList t C.gaps = qpre ++ [0])
    (hlen : qpre.length = rest.length)
    (hrest : rest ≠ [])
    (hneq :
      first ≠ (first :: rest).getLast (by simp)) :
    first.1 ≠ s ∧
      ((first :: rest).getLast (by simp)).1 ≠ s := by
  have hdelta1 : delta < 1 := by linarith
  have htpos :
      0 < t :=
    sendov_scale_pos (by omega : 1 ≤ n) hdelta0 ht
  have hlampos : 0 < lam := by
    rw [hlam]
    exact div_pos Real.pi_pos htpos
  have hsmall :=
    displayed_wrap_zero_gap_actual_angle_le_delta_lam
      hp hcap hn hdelta0 hdelta1 ht hlam
      i C hexp hsupport first rest hrays
      qpre hq hlen hrest hneq
  let last : OtherVertex i :=
    (first :: rest).getLast (by simp)
  constructor
  · intro hfirstS
    have hsLast : s ≠ last.1 := by
      intro hsl
      apply hneq
      apply Subtype.ext
      calc
        first.1 = s := hfirstS
        _ = last.1 := hsl
    have hlower :=
      delta_mul_lam_lt_outer_angle_of_sharp
        hp hcap hdeltaHalf hlampos
        hsi hsLast last.2.symm hs
    have hsmall' :
        EuclideanGeometry.angle (p s) (p i) (p last.1) ≤
          delta * lam := by
      rw [EuclideanGeometry.angle_comm]
      simpa [last, hfirstS] using hsmall
    linarith
  · intro hlastS
    have hsFirst : s ≠ first.1 := by
      intro hsf
      apply hneq
      apply Subtype.ext
      calc
        first.1 = s := hsf.symm
        _ = last.1 := hlastS.symm
    have hlower :=
      delta_mul_lam_lt_outer_angle_of_sharp
        hp hcap hdeltaHalf hlampos
        hsi hsFirst first.2.symm hs
    have hsmall' :
        EuclideanGeometry.angle (p s) (p i) (p first.1) ≤
          delta * lam := by
      simpa [last, hlastS] using hsmall
    linarith

#print axioms displayed_ordinary_zero_gap_endpoints_ne_sharp
#print axioms displayed_wrap_zero_gap_endpoints_ne_sharp

end JSP000404Research
