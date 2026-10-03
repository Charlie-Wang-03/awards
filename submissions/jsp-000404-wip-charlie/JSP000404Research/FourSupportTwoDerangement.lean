import JSP000404Research.QTTTThreeSupportSmallPairMatching
import JSP000404Research.ProjectionQTTTSmallPair
import Mathlib.Tactic

/-!
# Four support-two centres reduce to nine derangement patterns

At each of four distinct support-two second-layer centres, the support-two
geometry produces one delta*lambda-small pair among the other three vertices.

A choice at a vertex is equivalently a choice of one of the three triangles
containing that vertex.  The global angle cap and delta < 1/2 imply that no
triangle can receive small angles at two of its vertices.  With four vertices
making four choices, the surviving incidence pattern is therefore a
derangement of the four vertices against the four triangles.  There are
exactly nine such patterns.

This module records that finite terminal directly.  It is intentionally
palette-free: no consecutive-band or transition-quotient hypothesis is used.
-/

namespace JSP000404Research

def FourSupportTwoDerangementPattern9
    {V : Type*}
    (p : V → Plane) (delta lam : ℝ)
    (a b c d : V) : Prop :=
  let A_bc :=
    EuclideanGeometry.angle (p b) (p a) (p c) ≤ delta * lam
  let A_bd :=
    EuclideanGeometry.angle (p b) (p a) (p d) ≤ delta * lam
  let A_cd :=
    EuclideanGeometry.angle (p c) (p a) (p d) ≤ delta * lam
  let B_ac :=
    EuclideanGeometry.angle (p a) (p b) (p c) ≤ delta * lam
  let B_ad :=
    EuclideanGeometry.angle (p a) (p b) (p d) ≤ delta * lam
  let B_cd :=
    EuclideanGeometry.angle (p c) (p b) (p d) ≤ delta * lam
  let C_ab :=
    EuclideanGeometry.angle (p a) (p c) (p b) ≤ delta * lam
  let C_ad :=
    EuclideanGeometry.angle (p a) (p c) (p d) ≤ delta * lam
  let C_bd :=
    EuclideanGeometry.angle (p b) (p c) (p d) ≤ delta * lam
  let D_ab :=
    EuclideanGeometry.angle (p a) (p d) (p b) ≤ delta * lam
  let D_ac :=
    EuclideanGeometry.angle (p a) (p d) (p c) ≤ delta * lam
  let D_bc :=
    EuclideanGeometry.angle (p b) (p d) (p c) ≤ delta * lam
  (A_bc ∧ B_ad ∧ C_ad ∧ D_bc) ∨
  (A_bc ∧ B_ad ∧ C_bd ∧ D_ac) ∨
  (A_bc ∧ B_cd ∧ C_ad ∧ D_ab) ∨
  (A_bd ∧ B_ac ∧ C_ad ∧ D_bc) ∨
  (A_bd ∧ B_ac ∧ C_bd ∧ D_ac) ∨
  (A_bd ∧ B_cd ∧ C_ab ∧ D_ac) ∨
  (A_cd ∧ B_ac ∧ C_bd ∧ D_ab) ∨
  (A_cd ∧ B_ad ∧ C_ab ∧ D_bc) ∨
  (A_cd ∧ B_cd ∧ C_ab ∧ D_ab)

theorem four_smallPairAmongOtherThree_reduce_to_derangement_nine
    {V : Type*}
    {p : V → Plane}
    (hp : Function.Injective p)
    (hcap : AngleCap p lam)
    {delta lam : ℝ}
    (hdeltaHalf : delta < (1 : ℝ) / 2)
    (hlampos : 0 < lam)
    {a b c d : V}
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d)
    (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d)
    (ha : SmallPairAmongOtherThree p delta lam a b c d)
    (hb : SmallPairAmongOtherThree p delta lam b a c d)
    (hc : SmallPairAmongOtherThree p delta lam c a b d)
    (hd : SmallPairAmongOtherThree p delta lam d a b c) :
    FourSupportTwoDerangementPattern9 p delta lam a b c d := by
  have hpat :=
    three_smallPairAmongOtherThree_reduce_to_eleven
      hp hcap hdeltaHalf hlampos
      hab hac had hbc hbd hcd
      ha hb hc

  have noA_bd_D_ab
      (hA :
        EuclideanGeometry.angle (p b) (p a) (p d) ≤ delta * lam)
      (hD :
        EuclideanGeometry.angle (p a) (p d) (p b) ≤ delta * lam) :
      False := by
    exact two_delta_small_angles_same_triangle_impossible
      hp hcap hdeltaHalf hlampos
      had hab hbd.symm
      (by simpa [EuclideanGeometry.angle_comm] using hA)
      hD

  have noB_ad_D_ab
      (hB :
        EuclideanGeometry.angle (p a) (p b) (p d) ≤ delta * lam)
      (hD :
        EuclideanGeometry.angle (p a) (p d) (p b) ≤ delta * lam) :
      False := by
    exact two_delta_small_angles_same_triangle_impossible
      hp hcap hdeltaHalf hlampos
      hbd hab.symm had.symm
      (by simpa [EuclideanGeometry.angle_comm] using hB)
      (by simpa [EuclideanGeometry.angle_comm] using hD)

  have noA_cd_D_ac
      (hA :
        EuclideanGeometry.angle (p c) (p a) (p d) ≤ delta * lam)
      (hD :
        EuclideanGeometry.angle (p a) (p d) (p c) ≤ delta * lam) :
      False := by
    exact two_delta_small_angles_same_triangle_impossible
      hp hcap hdeltaHalf hlampos
      had hac hcd.symm
      (by simpa [EuclideanGeometry.angle_comm] using hA)
      hD

  have noC_ad_D_ac
      (hC :
        EuclideanGeometry.angle (p a) (p c) (p d) ≤ delta * lam)
      (hD :
        EuclideanGeometry.angle (p a) (p d) (p c) ≤ delta * lam) :
      False := by
    exact two_delta_small_angles_same_triangle_impossible
      hp hcap hdeltaHalf hlampos
      hcd hac.symm had.symm
      (by simpa [EuclideanGeometry.angle_comm] using hC)
      (by simpa [EuclideanGeometry.angle_comm] using hD)

  have noB_cd_D_bc
      (hB :
        EuclideanGeometry.angle (p c) (p b) (p d) ≤ delta * lam)
      (hD :
        EuclideanGeometry.angle (p b) (p d) (p c) ≤ delta * lam) :
      False := by
    exact two_delta_small_angles_same_triangle_impossible
      hp hcap hdeltaHalf hlampos
      hbd hbc hcd.symm
      (by simpa [EuclideanGeometry.angle_comm] using hB)
      hD

  have noC_bd_D_bc
      (hC :
        EuclideanGeometry.angle (p b) (p c) (p d) ≤ delta * lam)
      (hD :
        EuclideanGeometry.angle (p b) (p d) (p c) ≤ delta * lam) :
      False := by
    exact two_delta_small_angles_same_triangle_impossible
      hp hcap hdeltaHalf hlampos
      hcd hbc.symm hbd.symm
      (by simpa [EuclideanGeometry.angle_comm] using hC)
      (by simpa [EuclideanGeometry.angle_comm] using hD)

  unfold ThreeSupportTwoCrossedPattern11 at hpat
  unfold SmallPairAmongOtherThree at hd
  unfold FourSupportTwoDerangementPattern9
  rcases hpat with
      h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 <;>
    rcases hd with hDab | hDac | hDbc
  · exact False.elim (noB_ad_D_ab h1.2.1 hDab)
  · exact False.elim (noC_ad_D_ac h1.2.2 hDac)
  · aesop
  · exact False.elim (noB_ad_D_ab h2.2.1 hDab)
  · aesop
  · exact False.elim (noC_bd_D_bc h2.2.2 hDbc)
  · aesop
  · exact False.elim (noC_ad_D_ac h3.2.2 hDac)
  · exact False.elim (noB_cd_D_bc h3.2.1 hDbc)
  · exact False.elim (noA_bd_D_ab h4.1 hDab)
  · exact False.elim (noC_ad_D_ac h4.2.2 hDac)
  · aesop
  · exact False.elim (noA_bd_D_ab h5.1 hDab)
  · aesop
  · exact False.elim (noC_bd_D_bc h5.2.2 hDbc)
  · exact False.elim (noA_bd_D_ab h6.1 hDab)
  · aesop
  · exact False.elim (noB_cd_D_bc h6.2.1 hDbc)
  · exact False.elim (noA_bd_D_ab h7.1 hDab)
  · exact False.elim (noC_ad_D_ac h7.2.2 hDac)
  · exact False.elim (noB_cd_D_bc h7.2.1 hDbc)
  · aesop
  · exact False.elim (noA_cd_D_ac h8.1 hDac)
  · exact False.elim (noC_bd_D_bc h8.2.2 hDbc)
  · exact False.elim (noB_ad_D_ab h9.2.1 hDab)
  · exact False.elim (noA_cd_D_ac h9.1 hDac)
  · aesop
  · exact False.elim (noB_ad_D_ab h10.2.1 hDab)
  · exact False.elim (noA_cd_D_ac h10.1 hDac)
  · exact False.elim (noC_bd_D_bc h10.2.2 hDbc)
  · aesop
  · exact False.elim (noA_cd_D_ac h11.1 hDac)
  · exact False.elim (noB_cd_D_bc h11.2.1 hDbc)

#print axioms four_smallPairAmongOtherThree_reduce_to_derangement_nine

/-- Geometric specialization: four distinct second-layer support-two centres
force one of the nine K4 derangement small-angle patterns. -/
theorem four_supportTwo_secondLayer_reduce_to_derangement_nine
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane}
    (hp : Function.Injective p)
    (hcap : AngleCap p lam)
    {lam t delta : ℝ} {n : ℕ}
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
