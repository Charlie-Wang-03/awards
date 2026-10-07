import JSP000404Research.ProjectionQTTTSmallPair
import Mathlib.Geometry.Euclidean.Triangle
import Mathlib.Tactic

/-!
# Finite matching classification for two support-two centres in Q/T/T/T

Two designated centres a,b each carry one delta-small pair among the other
three vertices.  There are nine pair combinations.  Two combinations put two
small angles into the same triangle and are impossible under the global angle
cap.  The remaining seven combinations are recorded explicitly as the finite
crossed terminal.
-/

namespace JSP000404Research

open Real

theorem two_delta_small_angles_same_triangle_impossible
    {V : Type*}
    {p : V → Plane}
    {delta lam : ℝ}
    (hp : Function.Injective p)
    (hcap : AngleCap p lam)
    (hdeltaHalf : delta < (1 : ℝ) / 2)
    (hlampos : 0 < lam)
    {a b c : V}
    (hab : a ≠ b)
    (hac : a ≠ c)
    (hbc : b ≠ c)
    (ha :
      EuclideanGeometry.angle (p b) (p a) (p c)
        ≤ delta * lam)
    (hb :
      EuclideanGeometry.angle (p a) (p b) (p c)
        ≤ delta * lam) :
    False := by
  have hc :
      EuclideanGeometry.angle (p a) (p c) (p b)
        ≤ Real.pi - lam :=
    hcap a c b hac hab hbc.symm
  have hsum :
      EuclideanGeometry.angle (p b) (p a) (p c) +
        EuclideanGeometry.angle (p a) (p c) (p b) +
        EuclideanGeometry.angle (p c) (p b) (p a)
        =
      Real.pi := by
    simpa [add_assoc, add_left_comm, add_comm,
      EuclideanGeometry.angle_comm (p c) (p b) (p a)] using
      (EuclideanGeometry.angle_add_angle_add_angle_eq_pi
        (p₁ := p b) (p₂ := p a) (p c)
        (hp.ne hab))
  have hb' :
      EuclideanGeometry.angle (p c) (p b) (p a)
        ≤ delta * lam := by
    simpa [EuclideanGeometry.angle_comm] using hb
  have hstrict : 2 * delta * lam < lam := by
    nlinarith
  nlinarith

def CrossedTwoCentreSmallPairPattern
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
  (A_bc ∧ B_ad) ∨
  (A_bc ∧ B_cd) ∨
  (A_bd ∧ B_ac) ∨
  (A_bd ∧ B_cd) ∨
  (A_cd ∧ B_ac) ∨
  (A_cd ∧ B_ad) ∨
  (A_cd ∧ B_cd)

theorem two_smallPairAmongOtherThree_reduce_to_crossed
    {V : Type*}
    {p : V → Plane}
    {delta lam : ℝ}
    (hp : Function.Injective p)
    (hcap : AngleCap p lam)
    (hdeltaHalf : delta < (1 : ℝ) / 2)
    (hlampos : 0 < lam)
    {a b c d : V}
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d)
    (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d)
    (ha : SmallPairAmongOtherThree p delta lam a b c d)
    (hb : SmallPairAmongOtherThree p delta lam b a c d) :
    CrossedTwoCentreSmallPairPattern p delta lam a b c d := by
  unfold SmallPairAmongOtherThree at ha hb
  unfold CrossedTwoCentreSmallPairPattern
  rcases ha with hA_bc | hA_bd | hA_cd <;>
    rcases hb with hB_ac | hB_ad | hB_cd
  · exact False.elim
      (two_delta_small_angles_same_triangle_impossible
        hp hcap hdeltaHalf hlampos
        hab hac hbc hA_bc hB_ac)
  · exact Or.inl ⟨hA_bc,hB_ad⟩
  · exact Or.inr (Or.inl ⟨hA_bc,hB_cd⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨hA_bd,hB_ac⟩))
  · exact False.elim
      (two_delta_small_angles_same_triangle_impossible
        hp hcap hdeltaHalf hlampos
        hab had hbd hA_bd hB_ad)
  · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨hA_bd,hB_cd⟩)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr
      (Or.inl ⟨hA_cd,hB_ac⟩))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr
      (Or.inr (Or.inl ⟨hA_cd,hB_ad⟩)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr
      (Or.inr (Or.inr ⟨hA_cd,hB_cd⟩)))))

#print axioms two_delta_small_angles_same_triangle_impossible
#print axioms two_smallPairAmongOtherThree_reduce_to_crossed


/-- Geometric compression: two designated support-two members of four
second-layer centres force one of the seven crossed small-angle patterns. -/
theorem two_supportTwo_secondLayer_four_crossed
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane}
    {lam t delta : ℝ} {n : ℕ}
    (hp : Function.Injective p)
    (hcap : AngleCap p lam)
    (hn3 : 3 ≤ n)
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
    (haSupport :
      positiveSupport (centreQuotient (C a) t) = 2)
    (hbSupport :
      positiveSupport (centreQuotient (C b) t) = 2) :
    CrossedTwoCentreSmallPairPattern p delta lam a b c d := by
  have haSmall :
      SmallPairAmongOtherThree p delta lam a b c d :=
    secondLayer_supportTwo_first_has_small_pair_among_three
      hp hcap hn3 hdelta0 hdeltaHalf ht hlam
      hab hac had hbc hbd hcd
      (C a) haSecond haSupport
  have hbSmall :
      SmallPairAmongOtherThree p delta lam b a c d :=
    secondLayer_supportTwo_first_has_small_pair_among_three
      hp hcap hn3 hdelta0 hdeltaHalf ht hlam
      hab.symm hbc hbd hac had hcd
      (C b) hbSecond hbSupport
  have htpos : 0 < t := by
    have hnposNat : 0 < n := by omega
    have hnposReal : (0 : ℝ) < (n : ℝ) := by
      exact_mod_cast hnposNat
    rw [ht]
    nlinarith
  have hlampos : 0 < lam := by
    rw [hlam]
    exact div_pos Real.pi_pos htpos
  exact two_smallPairAmongOtherThree_reduce_to_crossed
    hp hcap hdeltaHalf hlampos
    hab hac had hbc hbd hcd
    haSmall hbSmall

#print axioms two_supportTwo_secondLayer_four_crossed

end JSP000404Research
