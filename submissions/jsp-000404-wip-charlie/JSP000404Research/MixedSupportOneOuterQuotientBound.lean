import JSP000404Research.MiddleHiddenCycleGeometry
import JSP000404Research.PositiveTransitionLargeAngleBound
import JSP000404Research.DeficitThreeSupportOneGeometry
import Mathlib.Geometry.Euclidean.Angle.Unoriented.TriangleInequality
import Mathlib.Tactic

/-!
# A support-one minimum bounds one outer quotient of a middle-hidden centre

Let top have exponent n-1, let a be an n-3/support-one minimum, and let i be
an n-3/support-three middle-hidden centre with three sign transitions.

Using the explicit middle-hidden cycle certificate

  [top, r, b, c, d],
  [qFirst, 0, qHidden, 0, qLast],

the support-one triangle bound gives

  ((n-2)-delta)*lambda <= angle(top,i,a).

The ray a is one of r,b,c,d.  The aligned zero-edge budget

  angle(r,i,b) + angle(c,i,d) <= delta*lambda

therefore transfers the support-one lower bound to at least one outer edge:

  ((n-2)-2*delta)*lambda <= angle(top,i,r)

or

  ((n-2)-2*delta)*lambda <= angle(d,i,top).

Since all three positive quotient positions are sign transitions, the
large-angle converse then forces the corresponding outer quotient to be at
most three.  Thus qFirst <= 3 or qLast <= 3.
-/

namespace JSP000404Research

open Real

theorem middle_hidden_outer_quotient_le_three_of_support_one
    {V : Type*} [LinearOrder V] [Fintype V] [DecidableEq V]
    {p : V → Plane}
    {lam t delta : ℝ} {n : ℕ}
    (hp : Function.Injective p)
    (hcap : AngleCap p lam)
    (hcard : Fintype.card V = 6)
    (hn : 4 ≤ n)
    (hdelta0 : 0 ≤ delta)
    (hdeltaHalf : delta < (1 : ℝ) / 2)
    (ht : t = (n : ℝ) + delta)
    (hlam : lam = Real.pi / t)
    {top a i : V}
    (hta : top ≠ a)
    (hit : i ≠ top)
    (hai : a ≠ i)
    (Ctop : CentreProjectiveCycle hp top)
    (Ca : CentreProjectiveCycle hp a)
    (Ci : CentreProjectiveCycle hp i)
    (hTop : centreExponent Ctop t = n - 1)
    (hA : centreExponent Ca t = n - 3)
    (hsupA :
      positiveSupport (centreQuotient Ca t) = 1)
    (hI : centreExponent Ci t = n - 3)
    (hsupI :
      positiveSupport (centreQuotient Ci t) = 3)
    (hmiddle :
      SupportThreePinnedMiddleShape
        (t := t) hp (show top ≠ i by simpa using hit) Ci)
    (hthree :
      ∃ first rest,
        Ci.rays = first :: rest ∧
        boolTransitionCountFrom
          (raySignAt hp i first)
          (liftedCentreSignPath hp i first rest) = 3) :
    ∃ H : MiddleHiddenPinnedCycleCertificate
        hp top i (show top ≠ i by simpa using hit) Ci t,
      H.qFirst ≤ 3 ∨ H.qLast ≤ 3 := by
  let htopi : top ≠ i := by simpa using hit
  let H :=
    Classical.choice
      (exists_middle_hidden_pinned_cycle_certificate
        hp hcard htopi Ci hmiddle)

  have hdelta1 : delta < 1 := by linarith
  have hsharp :
      SharpAt p delta lam top :=
    concrete_unit_deficit_is_sharp
      hp hcap (by omega : 2 ≤ n)
      hdelta0 hdelta1 ht hlam
      top Ctop hTop

  have hlargeA :
      (((n - 2 : ℕ) : ℝ) - delta) * lam ≤
        EuclideanGeometry.angle (p top) (p i) (p a) :=
    sharp_and_deficit_three_support_one_force_large_outer_angle
      hp hcap hn hdelta0 ht hlam
      hta hit.symm hai
      hsharp Ca hA hsupA

  have hsmall :=
    H.zero_edge_sum_le_delta_lam
      hp hcap hn hdelta0 hdeltaHalf ht hlam
      hI hsupI

  have hsmallRB :
      EuclideanGeometry.angle (p H.r.1) (p i) (p H.b.1)
        ≤ delta * lam := by
    have hnonneg :
        0 ≤ EuclideanGeometry.angle (p H.c.1) (p i) (p H.d.1) :=
      EuclideanGeometry.angle_nonneg _ _ _
    linarith

  have hsmallCD :
      EuclideanGeometry.angle (p H.c.1) (p i) (p H.d.1)
        ≤ delta * lam := by
    have hnonneg :
        0 ≤ EuclideanGeometry.angle (p H.r.1) (p i) (p H.b.1) :=
      EuclideanGeometry.angle_nonneg _ _ _
    linarith

  have haTop : a ≠ top := hta.symm
  have hcover :=
    H.covers_every_other_nonTop hai haTop

  have hOuter :
      (((n - 2 : ℕ) : ℝ) - 2 * delta) * lam ≤
          EuclideanGeometry.angle (p top) (p i) (p H.r.1)
        ∨
      (((n - 2 : ℕ) : ℝ) - 2 * delta) * lam ≤
          EuclideanGeometry.angle (p H.d.1) (p i) (p top) := by
    rcases hcover with har | hab | hac | had
    · left
      rw [har] at hlargeA
      nlinarith
    · left
      rw [hab] at hlargeA
      have hpath :=
        EuclideanGeometry.angle_le_angle_add_angle
          (p i) (p top) (p H.r.1) (p H.b.1)
      nlinarith
    · right
      rw [hac] at hlargeA
      have hpath :=
        EuclideanGeometry.angle_le_angle_add_angle
          (p i) (p top) (p H.d.1) (p H.c.1)
      have hcommOuter :
          EuclideanGeometry.angle (p top) (p i) (p H.d.1) =
            EuclideanGeometry.angle (p H.d.1) (p i) (p top) :=
        EuclideanGeometry.angle_comm _ _ _
      have hcommSmall :
          EuclideanGeometry.angle (p H.d.1) (p i) (p H.c.1) =
            EuclideanGeometry.angle (p H.c.1) (p i) (p H.d.1) :=
        EuclideanGeometry.angle_comm _ _ _
      rw [hcommOuter, hcommSmall] at hpath
      nlinarith
    · right
      rw [had] at hlargeA
      have hcomm :
          EuclideanGeometry.angle (p top) (p i) (p H.d.1) =
            EuclideanGeometry.angle (p H.d.1) (p i) (p top) :=
        EuclideanGeometry.angle_comm _ _ _
      rw [hcomm] at hlargeA
      nlinarith

  obtain ⟨firstT, restT, hraysT, htransT⟩ := hthree
  have hrestT : restT ≠ [] := by
    intro hnil
    have hlen := H.ray_length_eq_five
    rw [hraysT, hnil] at hlen
    simp at hlen

  have htpos :
      0 < t :=
    sendov_scale_pos (by omega : 1 ≤ n) hdelta0 ht
  have htone :
      1 ≤ t :=
    sendov_scale_one_le (by omega : 1 ≤ n) hdelta0 ht

  have hsupportList :
      listPositiveCount (quotientList t Ci.gaps) = 3 := by
    rw [← centreQuotient_ofFn Ci t,
        listPositiveCount_ofFn_eq_positiveSupport]
    exact hsupI

  have hrel :=
    centre_three_transition_large_positive_quotients_le_three
      hp hcap (by omega : 2 ≤ n)
      hdelta0 hdeltaHalf htpos htone ht hlam
      i Ci firstT restT hraysT hrestT
      htransT hsupportList

  have hrelRot :=
    largePositiveTransitionQuotientLeThree_rotate hrel H.k

  obtain ⟨first0, rest0, hrays0, hAngles0⟩ :=
    H.rotated_actual_angles
  have hcons :
      firstT :: restT = first0 :: rest0 := by
    rw [← hraysT, ← hrays0]
  have hfirst : firstT = first0 := (List.cons.inj hcons).1
  have hrest : restT = rest0 := (List.cons.inj hcons).2
  subst first0
  subst rest0

  unfold LargePositiveTransitionQuotientLeThree at hrelRot
  rw [H.quotients_rotate, hAngles0] at hrelRot

  cases hrelRot with
  | cons hqFirst htail1 =>
      cases htail1 with
      | cons _hzero1 htail2 =>
          cases htail2 with
          | cons _hHidden htail3 =>
              cases htail3 with
              | cons _hzero2 htail4 =>
                  cases htail4 with
                  | cons hqLast _ =>
                      refine ⟨H, ?_⟩
                      rcases hOuter with hFirstLarge | hLastLarge
                      · left
                        apply hqFirst
                        · omega
                        · exact hFirstLarge
                      · right
                        apply hqLast
                        · omega
                        · exact hLastLarge

#print axioms middle_hidden_outer_quotient_le_three_of_support_one

end JSP000404Research
