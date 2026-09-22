import JSP000404Research.GeneralZeroGapActualAngle
import JSP000404Research.GeneralSharpAvoidsZeroGap
import Mathlib.Tactic

/-!
# Natural adjacent-cut wrappers for arbitrary zero gaps

GeneralZeroGapActualAngle uses the low-level decomposition expected by
centre_gap_eq_ordinary_cut:

  first :: (before ++ right :: tail).

For cyclic pinning arguments it is more convenient to expose an ordinary
adjacent pair directly:

  prefix ++ left :: right :: suffix.

This file translates between the two forms.  It also provides the corresponding
sharp-ray avoidance wrapper.
-/

namespace JSP000404Research

theorem adjacent_zero_gap_actual_angle_le_delta_lam
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane}
    (hp : Function.Injective p)
    (hcap : AngleCap p lam)
    {lam t delta : ℝ} {n : ℕ}
    (hn : 3 ≤ n)
    (hdelta0 : 0 ≤ delta)
    (hdelta1 : delta < 1)
    (ht : t = (n : ℝ) + delta)
    (hlam : lam = Real.pi / t)
    (i : V)
    (C : CentreProjectiveCycle hp i)
    (hexp : centreExponent C t = n - 2)
    (hsupport :
      positiveSupport (centreQuotient C t) = 2)
    (prefix suffix : List (OtherVertex i))
    (left right : OtherVertex i)
    (hrays :
      C.rays = prefix ++ left :: right :: suffix)
    (qpre qpost : List ℕ)
    (hq :
      quotientList t C.gaps = qpre ++ 0 :: qpost)
    (hlen : qpre.length = prefix.length)
    (hlr : left ≠ right) :
    EuclideanGeometry.angle
        (p left.1) (p i) (p right.1)
      ≤ delta * lam := by
  cases prefix with
  | nil =>
      exact displayed_ordinary_zero_gap_actual_angle_le_delta_lam
        hp hcap hn hdelta0 hdelta1 ht hlam
        i C hexp hsupport
        left right [] suffix
        (by simpa using hrays)
        qpre qpost hq
        (by simpa using hlen)
        hlr
  | cons first pre =>
      have hrays' :
          C.rays =
            first :: ((pre ++ [left]) ++ right :: suffix) := by
        simpa [List.append_assoc] using hrays
      have hlen' :
          qpre.length = (pre ++ [left]).length := by
        simpa using hlen
      have hlast :
          (first :: (pre ++ [left])).getLast (by simp) = left := by
        simp
      have h :=
        displayed_ordinary_zero_gap_actual_angle_le_delta_lam
          hp hcap hn hdelta0 hdelta1 ht hlam
          i C hexp hsupport
          first right (pre ++ [left]) suffix
          hrays' qpre qpost hq hlen'
          (by simpa [hlast] using hlr)
      simpa [hlast] using h

theorem adjacent_zero_gap_endpoints_ne_sharp
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
    (prefix suffix : List (OtherVertex i))
    (left right : OtherVertex i)
    (hrays :
      C.rays = prefix ++ left :: right :: suffix)
    (qpre qpost : List ℕ)
    (hq :
      quotientList t C.gaps = qpre ++ 0 :: qpost)
    (hlen : qpre.length = prefix.length)
    (hlr : left ≠ right) :
    left.1 ≠ s ∧ right.1 ≠ s := by
  have hdelta1 : delta < 1 := by linarith
  have htpos :
      0 < t :=
    sendov_scale_pos (by omega : 1 ≤ n) hdelta0 ht
  have hlampos : 0 < lam := by
    rw [hlam]
    exact div_pos Real.pi_pos htpos
  have hsmall :=
    adjacent_zero_gap_actual_angle_le_delta_lam
      hp hcap hn hdelta0 hdelta1 ht hlam
      i C hexp hsupport prefix suffix left right
      hrays qpre qpost hq hlen hlr
  constructor
  · intro hleft
    have hsRight : s ≠ right.1 := by
      intro hright
      apply hlr
      apply Subtype.ext
      calc
        left.1 = s := hleft
        _ = right.1 := hright
    have hlower :=
      delta_mul_lam_lt_outer_angle_of_sharp
        hp hcap hdeltaHalf hlampos
        hsi hsRight right.2.symm hs
    have hsmall' :
        EuclideanGeometry.angle (p s) (p i) (p right.1)
          ≤ delta * lam := by
      simpa [hleft] using hsmall
    linarith
  · intro hright
    have hsLeft : s ≠ left.1 := by
      intro hleft
      apply hlr
      apply Subtype.ext
      calc
        left.1 = s := hleft.symm
        _ = right.1 := hright.symm
    have hlower :=
      delta_mul_lam_lt_outer_angle_of_sharp
        hp hcap hdeltaHalf hlampos
        hsi hsLeft left.2.symm hs
    have hsmall' :
        EuclideanGeometry.angle (p s) (p i) (p left.1)
          ≤ delta * lam := by
      rw [EuclideanGeometry.angle_comm]
      simpa [hright] using hsmall
    linarith

#print axioms adjacent_zero_gap_actual_angle_le_delta_lam
#print axioms adjacent_zero_gap_endpoints_ne_sharp

end JSP000404Research
