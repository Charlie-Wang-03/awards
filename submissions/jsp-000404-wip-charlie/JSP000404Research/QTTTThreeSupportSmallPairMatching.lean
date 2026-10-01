import JSP000404Research.ProjectionQTTTSmallPair
import JSP000404Research.QTTTSmallPairMatching
import Mathlib.Tactic

/-!
# Three-support-two small-pair matching

For three designated support-two centres a,b,c among four vertices a,b,c,d,
each centre has one delta*lambda-small pair among the other three vertices.
There are 27 raw pair choices.

Six pair-incidence types put one small angle at each of two centres of the same
triangle and are impossible under the global angle cap.  Eliminating all raw
cases containing one of those incidences leaves exactly eleven crossed
patterns.  This file records that finite reduction explicitly.
-/

namespace JSP000404Research

def ThreeSupportTwoCrossedPattern11
    {V : Type*}
    (p : V → Plane) (delta lam : ℝ)
    (a b c d : V) : Prop :=
  let A_bc := EuclideanGeometry.angle (p b) (p a) (p c) ≤ delta * lam
  let A_bd := EuclideanGeometry.angle (p b) (p a) (p d) ≤ delta * lam
  let A_cd := EuclideanGeometry.angle (p c) (p a) (p d) ≤ delta * lam
  let B_ac := EuclideanGeometry.angle (p a) (p b) (p c) ≤ delta * lam
  let B_ad := EuclideanGeometry.angle (p a) (p b) (p d) ≤ delta * lam
  let B_cd := EuclideanGeometry.angle (p c) (p b) (p d) ≤ delta * lam
  let C_ab := EuclideanGeometry.angle (p a) (p c) (p b) ≤ delta * lam
  let C_ad := EuclideanGeometry.angle (p a) (p c) (p d) ≤ delta * lam
  let C_bd := EuclideanGeometry.angle (p b) (p c) (p d) ≤ delta * lam
  (A_bc ∧ B_ad ∧ C_ad) ∨
  (A_bc ∧ B_ad ∧ C_bd) ∨
  (A_bc ∧ B_cd ∧ C_ad) ∨
  (A_bd ∧ B_ac ∧ C_ad) ∨
  (A_bd ∧ B_ac ∧ C_bd) ∨
  (A_bd ∧ B_cd ∧ C_ab) ∨
  (A_bd ∧ B_cd ∧ C_ad) ∨
  (A_cd ∧ B_ac ∧ C_bd) ∨
  (A_cd ∧ B_ad ∧ C_ab) ∨
  (A_cd ∧ B_ad ∧ C_bd) ∨
  (A_cd ∧ B_cd ∧ C_ab)

theorem three_smallPairAmongOtherThree_reduce_to_eleven
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
    (hc : SmallPairAmongOtherThree p delta lam c a b d) :
    ThreeSupportTwoCrossedPattern11 p delta lam a b c d := by
  unfold SmallPairAmongOtherThree at ha hb hc
  unfold ThreeSupportTwoCrossedPattern11

  have noABc
      (hA : EuclideanGeometry.angle (p b) (p a) (p c) ≤ delta * lam)
      (hB : EuclideanGeometry.angle (p a) (p b) (p c) ≤ delta * lam) :
      False :=
    two_delta_small_angles_same_triangle_impossible
      hp hcap hdeltaHalf hlampos hab hac hbc hA hB

  have noABd
      (hA : EuclideanGeometry.angle (p b) (p a) (p d) ≤ delta * lam)
      (hB : EuclideanGeometry.angle (p a) (p b) (p d) ≤ delta * lam) :
      False :=
    two_delta_small_angles_same_triangle_impossible
      hp hcap hdeltaHalf hlampos hab had hbd hA hB

  have noACb
      (hA : EuclideanGeometry.angle (p b) (p a) (p c) ≤ delta * lam)
      (hC : EuclideanGeometry.angle (p a) (p c) (p b) ≤ delta * lam) :
      False := by
    have hA' :
        EuclideanGeometry.angle (p c) (p a) (p b) ≤ delta * lam := by
      simpa [EuclideanGeometry.angle_comm] using hA
    exact two_delta_small_angles_same_triangle_impossible
      hp hcap hdeltaHalf hlampos
      hac hab hbc.symm hA' hC

  have noACd
      (hA : EuclideanGeometry.angle (p c) (p a) (p d) ≤ delta * lam)
      (hC : EuclideanGeometry.angle (p a) (p c) (p d) ≤ delta * lam) :
      False :=
    two_delta_small_angles_same_triangle_impossible
      hp hcap hdeltaHalf hlampos
      hac had hcd hA hC

  have noBCa
      (hB : EuclideanGeometry.angle (p a) (p b) (p c) ≤ delta * lam)
      (hC : EuclideanGeometry.angle (p a) (p c) (p b) ≤ delta * lam) :
      False := by
    have hB' :
        EuclideanGeometry.angle (p c) (p b) (p a) ≤ delta * lam := by
      simpa [EuclideanGeometry.angle_comm] using hB
    have hC' :
        EuclideanGeometry.angle (p b) (p c) (p a) ≤ delta * lam := by
      simpa [EuclideanGeometry.angle_comm] using hC
    exact two_delta_small_angles_same_triangle_impossible
      hp hcap hdeltaHalf hlampos
      hbc hab.symm hac.symm hB' hC'

  have noBCd
      (hB : EuclideanGeometry.angle (p c) (p b) (p d) ≤ delta * lam)
      (hC : EuclideanGeometry.angle (p b) (p c) (p d) ≤ delta * lam) :
      False :=
    two_delta_small_angles_same_triangle_impossible
      hp hcap hdeltaHalf hlampos
      hbc hbd hcd hB hC

  rcases ha with hA_bc | hA_bd | hA_cd <;>
    rcases hb with hB_ac | hB_ad | hB_cd <;>
    rcases hc with hC_ab | hC_ad | hC_bd
  · exact False.elim (noABc hA_bc hB_ac)
  · exact False.elim (noABc hA_bc hB_ac)
  · exact False.elim (noABc hA_bc hB_ac)
  · exact False.elim (noACb hA_bc hC_ab)
  · exact Or.inl ⟨hA_bc,hB_ad,hC_ad⟩
  · exact Or.inr (Or.inl ⟨hA_bc,hB_ad,hC_bd⟩)
  · exact False.elim (noACb hA_bc hC_ab)
  · exact Or.inr (Or.inr (Or.inl ⟨hA_bc,hB_cd,hC_ad⟩))
  · exact False.elim (noBCd hB_cd hC_bd)
  · exact False.elim (noBCa hB_ac hC_ab)
  · exact Or.inr (Or.inr (Or.inr
      (Or.inl ⟨hA_bd,hB_ac,hC_ad⟩)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr
      (Or.inl ⟨hA_bd,hB_ac,hC_bd⟩))))
  · exact False.elim (noABd hA_bd hB_ad)
  · exact False.elim (noABd hA_bd hB_ad)
  · exact False.elim (noABd hA_bd hB_ad)
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      (Or.inl ⟨hA_bd,hB_cd,hC_ab⟩)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      (Or.inr (Or.inl ⟨hA_bd,hB_cd,hC_ad⟩))))))
  · exact False.elim (noBCd hB_cd hC_bd)
  · exact False.elim (noBCa hB_ac hC_ab)
  · exact False.elim (noACd hA_cd hC_ad)
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      (Or.inr (Or.inr (Or.inl ⟨hA_cd,hB_ac,hC_bd⟩)))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      (Or.inr (Or.inr (Or.inr
        (Or.inl ⟨hA_cd,hB_ad,hC_ab⟩))))))))
  · exact False.elim (noACd hA_cd hC_ad)
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      (Or.inr (Or.inr (Or.inr (Or.inr
        (Or.inl ⟨hA_cd,hB_ad,hC_bd⟩)))))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      (Or.inr (Or.inr (Or.inr (Or.inr
        (Or.inr ⟨hA_cd,hB_cd,hC_ab⟩)))))))))
  · exact False.elim (noACd hA_cd hC_ad)
  · exact False.elim (noBCd hB_cd hC_bd)

#print axioms three_smallPairAmongOtherThree_reduce_to_eleven

end JSP000404Research
