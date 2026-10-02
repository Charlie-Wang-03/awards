import JSP000404Research.ThreeWholeCubePatternSevenTen
import Mathlib.Tactic

/-!
# Nine-state reduction beside a support-one fourth centre

Starting from ThreeSupportTwoCrossedPattern11 at support-two centres a,b,c,
assume the fourth centre d supplies the support-one narrow-cone bounds on all
three angles between a,b,c.

Patterns 7 and 10 are impossible by ThreeWholeCubePatternSevenTen, leaving the
nine explicit states recorded here.
-/

namespace JSP000404Research

def ThreeSupportTwoCrossedPattern9
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
  (A_cd ∧ B_ac ∧ C_bd) ∨
  (A_cd ∧ B_ad ∧ C_ab) ∨
  (A_cd ∧ B_cd ∧ C_ab)

theorem eleven_reduce_to_nine_beside_supportOne
    {V : Type*} {p : V → Plane}
    (hp : Function.Injective p)
    {lam t delta : ℝ} {n : ℕ}
    (hn4 : 4 ≤ n)
    (hdelta0 : 0 ≤ delta)
    (hdeltaHalf : delta < (1 : ℝ) / 2)
    (ht : t = (n : ℝ) + delta)
    (hlam : lam = Real.pi / t)
    {a b c d : V}
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d)
    (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d)
    (h11 : ThreeSupportTwoCrossedPattern11 p delta lam a b c d)
    (hdAB :
      EuclideanGeometry.angle (p a) (p d) (p b)
        ≤ (1 + delta) * lam)
    (hdAC :
      EuclideanGeometry.angle (p a) (p d) (p c)
        ≤ (1 + delta) * lam)
    (hdBC :
      EuclideanGeometry.angle (p b) (p d) (p c)
        ≤ (1 + delta) * lam) :
    ThreeSupportTwoCrossedPattern9 p delta lam a b c d := by
  unfold ThreeSupportTwoCrossedPattern11 at h11
  unfold ThreeSupportTwoCrossedPattern9
  rcases h11 with h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11'
  · exact Or.inl h1
  · exact Or.inr (Or.inl h2)
  · exact Or.inr (Or.inr (Or.inl h3))
  · exact Or.inr (Or.inr (Or.inr (Or.inl h4)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h5))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h6)))))
  · exact False.elim
      (threeSupport_pattern7_impossible_beside_supportOne
        hp hn4 hdelta0 hdeltaHalf ht hlam
        hab hac had hbc hbd hcd
        h7 hdAB hdAC hdBC)
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      (Or.inr (Or.inl h8))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      (Or.inr (Or.inr (Or.inl h9)))))))
  · exact False.elim
      (threeSupport_pattern10_impossible_beside_supportOne
        hp hn4 hdelta0 hdeltaHalf ht hlam
        hab hac had hbc hbd hcd
        h10 hdAB hdAC hdBC)
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      (Or.inr (Or.inr (Or.inr h11')))))))

#print axioms eleven_reduce_to_nine_beside_supportOne


/-- Geometric support specialization: three second-layer support-two centres
beside one second-layer support-one centre reduce directly to the nine-state
terminal. -/
theorem threeSupportTwo_oneSupportOne_reduce_to_nine
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane}
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
    (C : ∀ v : V, CentreProjectiveCycle hp v)
    (haSecond : centreExponent (C a) t = n - 2)
    (hbSecond : centreExponent (C b) t = n - 2)
    (hcSecond : centreExponent (C c) t = n - 2)
    (hdSecond : centreExponent (C d) t = n - 2)
    (haSupport :
      positiveSupport (centreQuotient (C a) t) = 2)
    (hbSupport :
      positiveSupport (centreQuotient (C b) t) = 2)
    (hcSupport :
      positiveSupport (centreQuotient (C c) t) = 2)
    (hdSupport :
      positiveSupport (centreQuotient (C d) t) = 1) :
    ThreeSupportTwoCrossedPattern9 p delta lam a b c d := by
  have h11 :=
    three_supportTwo_secondLayer_four_reduce_to_eleven
      hp hcap (by omega : 3 ≤ n)
      hdelta0 hdeltaHalf ht hlam
      hab hac had hbc hbd hcd
      C haSecond hbSecond hcSecond
      haSupport hbSupport hcSupport

  have hdelta1 : delta < 1 := by linarith
  let Hd :=
    Classical.choice
      (exists_highExponentTransitionIntervalCertificate
        hp hcap (by omega : 1 ≤ n)
        hdelta0 hdelta1 ht hlam
        d (C d) (by rw [hdSecond]; omega))

  have hdAB :
      EuclideanGeometry.angle (p a) (p d) (p b)
        ≤ (1 + delta) * lam :=
    secondLayer_supportOne_all_angles_le_one_add_delta_lam
      hp (by omega : 3 ≤ n) hdelta0 ht hlam
      (C d) hdSecond hdSupport Hd
      had hbd
  have hdAC :
      EuclideanGeometry.angle (p a) (p d) (p c)
        ≤ (1 + delta) * lam :=
    secondLayer_supportOne_all_angles_le_one_add_delta_lam
      hp (by omega : 3 ≤ n) hdelta0 ht hlam
      (C d) hdSecond hdSupport Hd
      had hcd
  have hdBC :
      EuclideanGeometry.angle (p b) (p d) (p c)
        ≤ (1 + delta) * lam :=
    secondLayer_supportOne_all_angles_le_one_add_delta_lam
      hp (by omega : 3 ≤ n) hdelta0 ht hlam
      (C d) hdSecond hdSupport Hd
      hbd hcd

  exact eleven_reduce_to_nine_beside_supportOne
    hp hn4 hdelta0 hdeltaHalf ht hlam
    hab hac had hbc hbd hcd
    h11 hdAB hdAC hdBC

#print axioms threeSupportTwo_oneSupportOne_reduce_to_nine

end JSP000404Research
