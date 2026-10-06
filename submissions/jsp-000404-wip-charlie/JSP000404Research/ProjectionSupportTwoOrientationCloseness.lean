import JSP000404Research.ProjectionQTTTSmallPair
import JSP000404Research.ProjectionOppositeSideRetainedAngle
import JSP000404Research.ProjectionSameSideSmallAngleBandCloseness
import JSP000404Research.FourCycleOwnerChoiceRigidity
import JSP000404Research.RetainedOrientation
import Mathlib.Tactic

/-!
# Same-orientation colour closeness at a support-two second-layer centre

At a second-layer support-two centre, any three marked rays contain a
delta*lambda-small pair.

If two chosen retained colours enter the centre and a third leaves it, both
mixed incoming/outgoing pairs are strictly larger than delta*lambda.  Hence
the forced small pair is the two incoming rays.  The same-side band estimate
then makes the two incoming colour labels one-step close.

The outgoing/outgoing version is symmetric.

This is the local geometric bridge needed to close the final 100/110
interior-source staircase profiles.
-/

namespace JSP000404Research
namespace ProjectionOrdered

open OrderedEdgeColoring

private theorem retainedColor_eq_of_full_color_eq
    {V : Type*} [LinearOrder V] {n : ℕ}
    (R : OrderedEdgeColoring V (n + 1))
    {u v : V} {c : Fin n}
    (hfull : R.color u v = c.castSucc)
    (hret : (R.color u v).val < n) :
    retainedColor R u v hret = c := by
  apply Fin.ext
  change (R.color u v).val = c.val
  rw [hfull]
  rfl

theorem supportTwo_two_incoming_one_outgoing_labels_oneStep
    {V : Type*} [Fintype V]
    {p : V → Plane}
    {lam t delta : ℝ} {n : ℕ}
    (hp : Function.Injective p)
    (hcap : AngleCap p lam)
    (hn3 : 3 ≤ n)
    (hdelta0 : 0 ≤ delta)
    (hdeltaHalf : delta < (1 : ℝ) / 2)
    (ht : t = (n : ℝ) + delta)
    (hlam : lam = Real.pi / t)
    {i : ProjectionOrdered V}
    (Ci : CentreProjectiveCycle (reindexedPoint_injective hp) i)
    (hiSecond : centreExponent Ci t = n - 2)
    (hiSupport : positiveSupport (centreQuotient Ci t) = 2)
    {x y z : Fin n}
    (hxy : x ≠ y)
    (hxIn :
      letI : LinearOrder (ProjectionOrdered V) :=
        projectionLinearOrder hp
      let R :=
        planarStandardResidualColoring
          hp hcap (by omega : 1 ≤ n)
          hdelta0 (by linarith : delta < 1) ht hlam
      x ∈ incomingRetained R i)
    (hyIn :
      letI : LinearOrder (ProjectionOrdered V) :=
        projectionLinearOrder hp
      let R :=
        planarStandardResidualColoring
          hp hcap (by omega : 1 ≤ n)
          hdelta0 (by linarith : delta < 1) ht hlam
      y ∈ incomingRetained R i)
    (hzOut :
      letI : LinearOrder (ProjectionOrdered V) :=
        projectionLinearOrder hp
      let R :=
        planarStandardResidualColoring
          hp hcap (by omega : 1 ≤ n)
          hdelta0 (by linarith : delta < 1) ht hlam
      z ∈ outgoingRetained R i) :
    NatOneStepClose x.val y.val := by
  letI : LinearOrder (ProjectionOrdered V) :=
    projectionLinearOrder hp
  have hn1 : 1 ≤ n := by omega
  have hdelta1 : delta < 1 := by linarith
  let R :=
    planarStandardResidualColoring
      hp hcap hn1 hdelta0 hdelta1 ht hlam

  have hxIn' : x ∈ incomingRetained R i := by
    simpa [R] using hxIn
  have hyIn' : y ∈ incomingRetained R i := by
    simpa [R] using hyIn
  have hzOut' : z ∈ outgoingRetained R i := by
    simpa [R] using hzOut

  obtain ⟨ux,huxi,hfullX⟩ :=
    (mem_incomingRetained_iff R i x).1 hxIn'
  obtain ⟨uy,huyi,hfullY⟩ :=
    (mem_incomingRetained_iff R i y).1 hyIn'
  obtain ⟨wz,hiwz,hfullZ⟩ :=
    (mem_outgoingRetained_iff R i z).1 hzOut'

  have hretX : (R.color ux i).val < n := by
    rw [hfullX]
    exact x.isLt
  have hretY : (R.color uy i).val < n := by
    rw [hfullY]
    exact y.isLt
  have hretZ : (R.color i wz).val < n := by
    rw [hfullZ]
    exact z.isLt

  have hcolX : retainedColor R ux i hretX = x :=
    retainedColor_eq_of_full_color_eq R hfullX hretX
  have hcolY : retainedColor R uy i hretY = y :=
    retainedColor_eq_of_full_color_eq R hfullY hretY

  have huxy : ux ≠ uy := by
    intro h
    subst uy
    apply hxy
    apply Fin.ext
    have hcast : x.castSucc = y.castSucc :=
      hfullX.symm.trans hfullY
    exact congrArg Fin.val hcast

  have hcapR : AngleCap (reindexedPoint p) lam :=
    angleCap_reindexed hcap
  have hsmall :=
    secondLayer_supportTwo_first_has_small_pair_among_three
      (reindexedPoint_injective hp) hcapR
      hn3 hdelta0 hdeltaHalf ht hlam
      (ne_of_lt huxi).symm
      (ne_of_lt huyi).symm
      (ne_of_lt hiwz)
      huxy
      (ne_of_lt (huxi.trans hiwz))
      (ne_of_lt (huyi.trans hiwz))
      Ci hiSecond hiSupport

  unfold SmallPairAmongOtherThree at hsmall
  rcases hsmall with hXY | hXZ | hYZ
  · rcases lt_or_gt_of_ne huxy with huxylt | hyuxlt
    · have hclose :=
        left_same_side_small_angle_labels_one_step_close
          hp hcap hn1 hdelta0 hdeltaHalf ht hlam
          huxylt huyi
          (by simpa [R] using hretX)
          (by simpa [R] using hretY)
          hXY
      have hclose' :
          NatOneStepClose
            (retainedColor R ux i hretX).val
            (retainedColor R uy i hretY).val := by
        simpa [NatOneStepClose, R] using hclose
      simpa [hcolX,hcolY] using hclose'
    · have hclose :=
        left_same_side_small_angle_labels_one_step_close
          hp hcap hn1 hdelta0 hdeltaHalf ht hlam
          hyuxlt huxi
          (by simpa [R] using hretY)
          (by simpa [R] using hretX)
          (by simpa [EuclideanGeometry.angle_comm] using hXY)
      have hclose' :
          NatOneStepClose
            (retainedColor R uy i hretY).val
            (retainedColor R ux i hretX).val := by
        simpa [NatOneStepClose, R] using hclose
      exact natOneStepClose_symm
        (by simpa [hcolY,hcolX] using hclose')
  · exact False.elim
      (opposite_side_retained_not_delta_small
        hp hcap hn1 hdelta0 hdelta1 ht hlam
        huxi hiwz
        (by simpa [R] using hretX)
        (by simpa [R] using hretZ)
        hXZ)
  · exact False.elim
      (opposite_side_retained_not_delta_small
        hp hcap hn1 hdelta0 hdelta1 ht hlam
        huyi hiwz
        (by simpa [R] using hretY)
        (by simpa [R] using hretZ)
        hYZ)

theorem supportTwo_two_outgoing_one_incoming_labels_oneStep
    {V : Type*} [Fintype V]
    {p : V → Plane}
    {lam t delta : ℝ} {n : ℕ}
    (hp : Function.Injective p)
    (hcap : AngleCap p lam)
    (hn3 : 3 ≤ n)
    (hdelta0 : 0 ≤ delta)
    (hdeltaHalf : delta < (1 : ℝ) / 2)
    (ht : t = (n : ℝ) + delta)
    (hlam : lam = Real.pi / t)
    {i : ProjectionOrdered V}
    (Ci : CentreProjectiveCycle (reindexedPoint_injective hp) i)
    (hiSecond : centreExponent Ci t = n - 2)
    (hiSupport : positiveSupport (centreQuotient Ci t) = 2)
    {x y z : Fin n}
    (hxy : x ≠ y)
    (hxOut :
      letI : LinearOrder (ProjectionOrdered V) :=
        projectionLinearOrder hp
      let R :=
        planarStandardResidualColoring
          hp hcap (by omega : 1 ≤ n)
          hdelta0 (by linarith : delta < 1) ht hlam
      x ∈ outgoingRetained R i)
    (hyOut :
      letI : LinearOrder (ProjectionOrdered V) :=
        projectionLinearOrder hp
      let R :=
        planarStandardResidualColoring
          hp hcap (by omega : 1 ≤ n)
          hdelta0 (by linarith : delta < 1) ht hlam
      y ∈ outgoingRetained R i)
    (hzIn :
      letI : LinearOrder (ProjectionOrdered V) :=
        projectionLinearOrder hp
      let R :=
        planarStandardResidualColoring
          hp hcap (by omega : 1 ≤ n)
          hdelta0 (by linarith : delta < 1) ht hlam
      z ∈ incomingRetained R i) :
    NatOneStepClose x.val y.val := by
  letI : LinearOrder (ProjectionOrdered V) :=
    projectionLinearOrder hp
  have hn1 : 1 ≤ n := by omega
  have hdelta1 : delta < 1 := by linarith
  let R :=
    planarStandardResidualColoring
      hp hcap hn1 hdelta0 hdelta1 ht hlam

  have hxOut' : x ∈ outgoingRetained R i := by
    simpa [R] using hxOut
  have hyOut' : y ∈ outgoingRetained R i := by
    simpa [R] using hyOut
  have hzIn' : z ∈ incomingRetained R i := by
    simpa [R] using hzIn

  obtain ⟨wx,hiwx,hfullX⟩ :=
    (mem_outgoingRetained_iff R i x).1 hxOut'
  obtain ⟨wy,hiwy,hfullY⟩ :=
    (mem_outgoingRetained_iff R i y).1 hyOut'
  obtain ⟨uz,huzi,hfullZ⟩ :=
    (mem_incomingRetained_iff R i z).1 hzIn'

  have hretX : (R.color i wx).val < n := by
    rw [hfullX]
    exact x.isLt
  have hretY : (R.color i wy).val < n := by
    rw [hfullY]
    exact y.isLt
  have hretZ : (R.color uz i).val < n := by
    rw [hfullZ]
    exact z.isLt

  have hcolX : retainedColor R i wx hretX = x :=
    retainedColor_eq_of_full_color_eq R hfullX hretX
  have hcolY : retainedColor R i wy hretY = y :=
    retainedColor_eq_of_full_color_eq R hfullY hretY

  have hwxy : wx ≠ wy := by
    intro h
    subst wy
    apply hxy
    apply Fin.ext
    have hcast : x.castSucc = y.castSucc :=
      hfullX.symm.trans hfullY
    exact congrArg Fin.val hcast

  have hcapR : AngleCap (reindexedPoint p) lam :=
    angleCap_reindexed hcap
  have hsmall :=
    secondLayer_supportTwo_first_has_small_pair_among_three
      (reindexedPoint_injective hp) hcapR
      hn3 hdelta0 hdeltaHalf ht hlam
      (ne_of_lt hiwx)
      (ne_of_lt hiwy)
      (ne_of_lt huzi).symm
      hwxy
      (ne_of_lt (huzi.trans hiwx)).symm
      (ne_of_lt (huzi.trans hiwy)).symm
      Ci hiSecond hiSupport

  unfold SmallPairAmongOtherThree at hsmall
  rcases hsmall with hXY | hXZ | hYZ
  · rcases lt_or_gt_of_ne hwxy with hwxylt | hywxlt
    · have hclose :=
        right_same_side_small_angle_labels_one_step_close
          hp hcap hn1 hdelta0 hdeltaHalf ht hlam
          hiwx hwxylt
          (by simpa [R] using hretX)
          (by simpa [R] using hretY)
          hXY
      have hclose' :
          NatOneStepClose
            (retainedColor R i wx hretX).val
            (retainedColor R i wy hretY).val := by
        simpa [NatOneStepClose, R] using hclose
      simpa [hcolX,hcolY] using hclose'
    · have hclose :=
        right_same_side_small_angle_labels_one_step_close
          hp hcap hn1 hdelta0 hdeltaHalf ht hlam
          hiwy hywxlt
          (by simpa [R] using hretY)
          (by simpa [R] using hretX)
          (by simpa [EuclideanGeometry.angle_comm] using hXY)
      have hclose' :
          NatOneStepClose
            (retainedColor R i wy hretY).val
            (retainedColor R i wx hretX).val := by
        simpa [NatOneStepClose, R] using hclose
      exact natOneStepClose_symm
        (by simpa [hcolY,hcolX] using hclose')
  · exact False.elim
      (opposite_side_retained_not_delta_small
        hp hcap hn1 hdelta0 hdelta1 ht hlam
        huzi hiwx
        (by simpa [R] using hretZ)
        (by simpa [R] using hretX)
        (by simpa [EuclideanGeometry.angle_comm] using hXZ))
  · exact False.elim
      (opposite_side_retained_not_delta_small
        hp hcap hn1 hdelta0 hdelta1 ht hlam
        huzi hiwy
        (by simpa [R] using hretZ)
        (by simpa [R] using hretY)
        (by simpa [EuclideanGeometry.angle_comm] using hYZ))

#print axioms supportTwo_two_incoming_one_outgoing_labels_oneStep
#print axioms supportTwo_two_outgoing_one_incoming_labels_oneStep

end ProjectionOrdered
end JSP000404Research
