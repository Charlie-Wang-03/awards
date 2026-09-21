import JSP000404Research.FourCentreSupportTwoSmallAngle
import JSP000404Research.ConcreteSharpCentre
import JSP000404Research.SharpOuterAngles
import Mathlib.Tactic

/-!
# Two support-two deficit-two centres cannot coexist outside a sharp centre

This closes the support-two/support-two branch of the four-centre terminal.

Let s be a sharp/unit-deficit centre and let a,b be two deficit-two centres
whose quotient support is two; let c be the fourth vertex.

At a, FourCentreSupportTwoSmallAngle produces a pair of non-a rays making
actual angle at most delta*lambda.  Any pair involving the sharp ray s makes,
by SharpOuterAngles, angle strictly larger than delta*lambda.  Since there are
only four vertices, the small pair must therefore be {b,c}.  Hence

  angle b-a-c <= delta*lambda.

The same argument at b gives

  angle a-b-c <= delta*lambda.

The third angle of triangle a-b-c is then strictly larger than pi-lambda
because 2*delta<1, contradicting the global angle cap.
-/

namespace JSP000404Research

open Real

theorem fin_four_exhaust_of_four_distinct
    {s a b c : Fin 4}
    (hsa : s ≠ a) (hsb : s ≠ b) (hsc : s ≠ c)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    ∀ x : Fin 4, x = s ∨ x = a ∨ x = b ∨ x = c := by
  classical
  have hset :
      ({s,a,b,c} : Finset (Fin 4)) = Finset.univ := by
    apply Finset.eq_univ_of_card
    simp [hsa, hsb, hsc, hab, hac, hbc,
      Ne.symm hsa, Ne.symm hsb, Ne.symm hsc,
      Ne.symm hab, Ne.symm hac, Ne.symm hbc]
  intro x
  have hx : x ∈ ({s,a,b,c} : Finset (Fin 4)) := by
    rw [hset]
    simp
  simpa using hx

/-- A small pair at an outer centre cannot use the sharp ray; in a four-point
configuration it must be the other two outer vertices. -/
theorem small_pair_at_outer_eq_other_outer_pair
    {p : Fin 4 → Plane}
    (hp : Function.Injective p)
    (hcap : AngleCap p lam)
    {delta lam : ℝ}
    (hdeltaHalf : delta < (1 : ℝ) / 2)
    (hlampos : 0 < lam)
    {s a b c : Fin 4}
    (hsa : s ≠ a) (hsb : s ≠ b) (hsc : s ≠ c)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hs : SharpAt p delta lam s)
    (x y : OtherVertex a)
    (hxy : x ≠ y)
    (hsmall :
      EuclideanGeometry.angle (p x.1) (p a) (p y.1) ≤
        delta * lam) :
    (x.1 = b ∧ y.1 = c) ∨
      (x.1 = c ∧ y.1 = b) := by
  have hxns : x.1 ≠ s := by
    intro hxs
    have hyns : y.1 ≠ s := by
      intro hys
      apply hxy
      apply Subtype.ext
      simpa [hxs] using hys
    have hsharp :=
      delta_mul_lam_lt_outer_angle_of_sharp
        hp hcap hdeltaHalf hlampos
        hsa hyns y.2 hs
    rw [hxs] at hsmall
    linarith
  have hyns : y.1 ≠ s := by
    intro hys
    have hxns' : x.1 ≠ s := hxns
    have hsharp :=
      delta_mul_lam_lt_outer_angle_of_sharp
        hp hcap hdeltaHalf hlampos
        hsa hxns' x.2 hs
    have hsmall' :
        EuclideanGeometry.angle (p s) (p a) (p x.1) ≤
          delta * lam := by
      rw [← EuclideanGeometry.angle_comm]
      simpa [hys] using hsmall
    linarith
  have hcover :=
    fin_four_exhaust_of_four_distinct
      hsa hsb hsc hab hac hbc
  have hxout : x.1 = b ∨ x.1 = c := by
    rcases hcover x.1 with hxs | hxa | hxb | hxc
    · exact False.elim (hxns hxs)
    · exact False.elim (x.2 hxa)
    · exact Or.inl hxb
    · exact Or.inr hxc
  have hyout : y.1 = b ∨ y.1 = c := by
    rcases hcover y.1 with hys | hya | hyb | hyc
    · exact False.elim (hyns hys)
    · exact False.elim (y.2 hya)
    · exact Or.inl hyb
    · exact Or.inr hyc
  rcases hxout with hxb | hxc <;>
    rcases hyout with hyb | hyc
  · exfalso
    apply hxy
    apply Subtype.ext
    rw [hxb, hyb]
  · exact Or.inl ⟨hxb, hyc⟩
  · exact Or.inr ⟨hxc, hyb⟩
  · exfalso
    apply hxy
    apply Subtype.ext
    rw [hxc, hyc]

theorem no_sharp_with_two_support_two_deficit_two_fin_four
    {p : Fin 4 → Plane}
    (hp : Function.Injective p)
    (hcap : AngleCap p lam)
    {lam t delta : ℝ} {n : ℕ}
    (hn : 3 ≤ n)
    (hdelta0 : 0 ≤ delta)
    (hdeltaHalf : delta < (1 : ℝ) / 2)
    (ht : t = (n : ℝ) + delta)
    (hlam : lam = Real.pi / t)
    {s a b c : Fin 4}
    (hsa : s ≠ a) (hsb : s ≠ b) (hsc : s ≠ c)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (Cs : CentreProjectiveCycle hp s)
    (Ca : CentreProjectiveCycle hp a)
    (Cb : CentreProjectiveCycle hp b)
    (hS : centreExponent Cs t = n - 1)
    (hA : centreExponent Ca t = n - 2)
    (hB : centreExponent Cb t = n - 2)
    (hsupA : positiveSupport (centreQuotient Ca t) = 2)
    (hsupB : positiveSupport (centreQuotient Cb t) = 2) :
    False := by
  have hdelta1 : delta < 1 := by linarith
  have htpos :=
    sendov_scale_pos (by omega : 1 ≤ n) hdelta0 ht
  have hlampos : 0 < lam := by
    rw [hlam]
    exact div_pos Real.pi_pos htpos
  have hsSharp :=
    concrete_unit_deficit_is_sharp
      hp hcap hn hdelta0 hdelta1 ht hlam
      s Cs hS
  obtain ⟨xa, ya, hxya, hsmallA⟩ :=
    exists_small_angle_pair_of_four_centre_deficit_two_support_two
      hp hcap hn hdelta0 hdeltaHalf ht hlam
      a Ca hA hsupA
  have hpairA :=
    small_pair_at_outer_eq_other_outer_pair
      hp hcap hdeltaHalf hlampos
      hsa hsb hsc hab hac hbc hsSharp
      xa ya hxya hsmallA
  have hangleA :
      EuclideanGeometry.angle (p b) (p a) (p c) ≤
        delta * lam := by
    rcases hpairA with h | h
    · simpa [h.1, h.2] using hsmallA
    · have h' := hsmallA
      rw [h.1, h.2] at h'
      simpa only [EuclideanGeometry.angle_comm] using h'
  obtain ⟨xb, yb, hxyb, hsmallB⟩ :=
    exists_small_angle_pair_of_four_centre_deficit_two_support_two
      hp hcap hn hdelta0 hdeltaHalf ht hlam
      b Cb hB hsupB
  have hpairB :
      (xb.1 = a ∧ yb.1 = c) ∨
        (xb.1 = c ∧ yb.1 = a) := by
    exact small_pair_at_outer_eq_other_outer_pair
      hp hcap hdeltaHalf hlampos
      hsb hsa hsc hab.symm hbc hac
      hsSharp xb yb hxyb hsmallB
  have hangleB :
      EuclideanGeometry.angle (p a) (p b) (p c) ≤
        delta * lam := by
    rcases hpairB with h | h
    · simpa [h.1, h.2] using hsmallB
    · have h' := hsmallB
      rw [h.1, h.2] at h'
      simpa only [EuclideanGeometry.angle_comm] using h'
  have hsum :=
    EuclideanGeometry.angle_add_angle_add_angle_eq_pi
      (p₁ := p b) (p₂ := p a) (p c)
      (hp.ne hab.symm)
  have hcommB :
      EuclideanGeometry.angle (p c) (p b) (p a) =
        EuclideanGeometry.angle (p a) (p b) (p c) :=
    EuclideanGeometry.angle_comm _ _ _
  rw [hcommB] at hsum
  have hcapC :
      EuclideanGeometry.angle (p a) (p c) (p b) ≤
        Real.pi - lam :=
    hcap a c b hac hab hbc.symm
  have hsmallSum :
      2 * delta * lam < lam := by
    nlinarith
  nlinarith

#print axioms fin_four_exhaust_of_four_distinct
#print axioms small_pair_at_outer_eq_other_outer_pair
#print axioms no_sharp_with_two_support_two_deficit_two_fin_four

end JSP000404Research
