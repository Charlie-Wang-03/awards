import JSP000404Research.FourSupportTwoDerangementExtremeMatrix
import Mathlib.Tactic

/-!
# Derangement elimination for an extreme-partner angle matrix

When a whole-cube partner, rather than the source, is the global extreme, the
source sits immediately next to that extreme.  The retained-code matrix then
has the following geometric shape on labels a=source, b=extreme partner and
c,d=the other two partners:

* triangle abc has a strict sub-lambda angle at b or c;
* triangle abd has a strict sub-lambda angle at b or d;
* triangle acd has a strict sub-lambda angle at c or d.

This abstract matrix alone already contradicts every one of the nine
all-support-two derangement patterns.
-/

namespace JSP000404Research

theorem fourSupportTwo_derangement_impossible_of_adjacentSource_matrix
    {V : Type*} {p : V → Plane}
    (hp : Function.Injective p)
    (hcap : AngleCap p lam)
    {lam t delta : ℝ} {n : ℕ}
    (hn4 : 4 ≤ n)
    (hdelta0 : 0 ≤ delta)
    (hdeltaHalf : delta < (1 : ℝ) / 2)
    (ht : t = (n : ℝ) + delta)
    (hlam : lam = Real.pi / t)
    {a b c d : V}
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d)
    (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d)
    (hpat :
      FourSupportTwoDerangementPattern9 p delta lam a b c d)
    (hABC :
      EuclideanGeometry.angle (p a) (p b) (p c) < lam
      ∨
      EuclideanGeometry.angle (p a) (p c) (p b) < lam)
    (hABD :
      EuclideanGeometry.angle (p a) (p b) (p d) < lam
      ∨
      EuclideanGeometry.angle (p a) (p d) (p b) < lam)
    (hACD :
      EuclideanGeometry.angle (p a) (p c) (p d) < lam
      ∨
      EuclideanGeometry.angle (p a) (p d) (p c) < lam) :
    False := by
  have killABC_A
      (hA :
        EuclideanGeometry.angle (p b) (p a) (p c)
          ≤ delta * lam) : False := by
    rcases hABC with hB | hC
    · exact delta_small_and_distinct_unit_angle_impossible
        hp hcap hn4 hdelta0 hdeltaHalf ht hlam
        hab hac hbc hA hB
    · exact delta_small_and_distinct_unit_angle_impossible
        hp hcap hn4 hdelta0 hdeltaHalf ht hlam
        hac hab hbc.symm
        (by simpa [EuclideanGeometry.angle_comm] using hA)
        hC

  have killABD_A
      (hA :
        EuclideanGeometry.angle (p b) (p a) (p d)
          ≤ delta * lam) : False := by
    rcases hABD with hB | hD
    · exact delta_small_and_distinct_unit_angle_impossible
        hp hcap hn4 hdelta0 hdeltaHalf ht hlam
        hab had hbd hA hB
    · exact delta_small_and_distinct_unit_angle_impossible
        hp hcap hn4 hdelta0 hdeltaHalf ht hlam
        had hab hbd.symm
        (by simpa [EuclideanGeometry.angle_comm] using hA)
        hD

  have killACD_A
      (hA :
        EuclideanGeometry.angle (p c) (p a) (p d)
          ≤ delta * lam) : False := by
    rcases hACD with hC | hD
    · exact delta_small_and_distinct_unit_angle_impossible
        hp hcap hn4 hdelta0 hdeltaHalf ht hlam
        hac had hcd hA hC
    · exact delta_small_and_distinct_unit_angle_impossible
        hp hcap hn4 hdelta0 hdeltaHalf ht hlam
        had hac hcd.symm
        (by simpa [EuclideanGeometry.angle_comm] using hA)
        hD

  have killACD_C_if_D
      (hCsmall :
        EuclideanGeometry.angle (p a) (p c) (p d)
          ≤ delta * lam)
      (hDunit :
        EuclideanGeometry.angle (p a) (p d) (p c) < lam) :
      False := by
    exact delta_small_and_distinct_unit_angle_impossible
      hp hcap hn4 hdelta0 hdeltaHalf ht hlam
      hcd hac.symm had.symm
      (by simpa [EuclideanGeometry.angle_comm] using hCsmall)
      (by simpa [EuclideanGeometry.angle_comm] using hDunit)

  have killACD_D_if_C
      (hDsmall :
        EuclideanGeometry.angle (p a) (p d) (p c)
          ≤ delta * lam)
      (hCunit :
        EuclideanGeometry.angle (p a) (p c) (p d) < lam) :
      False := by
    exact delta_small_and_distinct_unit_angle_impossible
      hp hcap hn4 hdelta0 hdeltaHalf ht hlam
      hcd.symm had.symm hac.symm
      (by simpa [EuclideanGeometry.angle_comm] using hDsmall)
      (by simpa [EuclideanGeometry.angle_comm] using hCunit)

  unfold FourSupportTwoDerangementPattern9 at hpat
  rcases hpat with h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9
  · rcases hACD with hC | hD
    · exact killABC_A h1.1
    · exact killACD_C_if_D h1.2.2.1 hD
  · rcases hACD with hC | hD
    · exact killACD_D_if_C h2.2.2.2 hC
    · exact killABC_A h2.1
  · rcases hACD with hC | hD
    · exact killABC_A h3.1
    · exact killACD_C_if_D h3.2.2.1 hD
  · rcases hACD with hC | hD
    · exact killABD_A h4.1
    · exact killACD_C_if_D h4.2.2.1 hD
  · rcases hACD with hC | hD
    · exact killACD_D_if_C h5.2.2.2 hC
    · exact killABD_A h5.1
  · rcases hACD with hC | hD
    · exact killACD_D_if_C h6.2.2.2 hC
    · exact killABD_A h6.1
  · exact killACD_A h7.1
  · exact killACD_A h8.1
  · exact killACD_A h9.1

#print axioms fourSupportTwo_derangement_impossible_of_adjacentSource_matrix

end JSP000404Research
