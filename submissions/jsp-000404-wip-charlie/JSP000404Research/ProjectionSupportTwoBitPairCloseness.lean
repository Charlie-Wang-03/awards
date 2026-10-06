import JSP000404Research.ProjectionSupportTwoOrientationCloseness
import JSP000404Research.RetainedBitOrientationLight
import Mathlib.Tactic

/-!
# Bit-profile to one-step retained-colour closeness at support-two centres

If two active retained colours have the same orientation bit and a third
active retained colour has the opposite bit, the same-orientation pair is
one-step close in band label.  This is a small wrapper around the incoming /
outgoing versions of the support-two orientation-closeness theorem.
-/

namespace JSP000404Research
namespace ProjectionOrdered

open OrderedEdgeColoring

theorem supportTwo_equal_bits_third_opposite_labels_oneStep
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
    (Ci :
      letI : LinearOrder (ProjectionOrdered V) :=
        projectionLinearOrder hp
      CentreProjectiveCycle (reindexedPoint_injective hp) i)
    (hiSecond :
      letI : LinearOrder (ProjectionOrdered V) :=
        projectionLinearOrder hp
      centreExponent Ci t = n - 2)
    (hiSupport :
      letI : LinearOrder (ProjectionOrdered V) :=
        projectionLinearOrder hp
      positiveSupport (centreQuotient Ci t) = 2)
    {x y z : Fin n}
    (hxy : x ≠ y)
    (hx :
      letI : LinearOrder (ProjectionOrdered V) :=
        projectionLinearOrder hp
      let R :=
        planarStandardResidualColoring
          hp hcap (by omega : 1 ≤ n)
          hdelta0 (by linarith : delta < 1) ht hlam
      x ∈ retainedActive R i)
    (hy :
      letI : LinearOrder (ProjectionOrdered V) :=
        projectionLinearOrder hp
      let R :=
        planarStandardResidualColoring
          hp hcap (by omega : 1 ≤ n)
          hdelta0 (by linarith : delta < 1) ht hlam
      y ∈ retainedActive R i)
    (hz :
      letI : LinearOrder (ProjectionOrdered V) :=
        projectionLinearOrder hp
      let R :=
        planarStandardResidualColoring
          hp hcap (by omega : 1 ≤ n)
          hdelta0 (by linarith : delta < 1) ht hlam
      z ∈ retainedActive R i)
    (hbitXY :
      letI : LinearOrder (ProjectionOrdered V) :=
        projectionLinearOrder hp
      let R :=
        planarStandardResidualColoring
          hp hcap (by omega : 1 ≤ n)
          hdelta0 (by linarith : delta < 1) ht hlam
      retainedBit R i x = retainedBit R i y)
    (hbitXZ :
      letI : LinearOrder (ProjectionOrdered V) :=
        projectionLinearOrder hp
      let R :=
        planarStandardResidualColoring
          hp hcap (by omega : 1 ≤ n)
          hdelta0 (by linarith : delta < 1) ht hlam
      retainedBit R i x ≠ retainedBit R i z) :
    NatOneStepClose x.val y.val := by
  letI : LinearOrder (ProjectionOrdered V) :=
    projectionLinearOrder hp
  let R :=
    planarStandardResidualColoring
      hp hcap (by omega : 1 ≤ n)
      hdelta0 (by linarith : delta < 1) ht hlam

  have hx' : x ∈ retainedActive R i := by simpa [R] using hx
  have hy' : y ∈ retainedActive R i := by simpa [R] using hy
  have hz' : z ∈ retainedActive R i := by simpa [R] using hz
  have hxyBit : retainedBit R i x = retainedBit R i y := by
    simpa [R] using hbitXY
  have hxzBit : retainedBit R i x ≠ retainedBit R i z := by
    simpa [R] using hbitXZ

  cases hbx : retainedBit R i x with
  | false =>
      have hby : retainedBit R i y = false := by
        rw [← hxyBit, hbx]
      have hbz : retainedBit R i z = true := by
        cases hzbit : retainedBit R i z
        · exact False.elim (hxzBit (by simp [hbx, hzbit]))
        · exact hzbit
      have hxOut :=
        mem_outgoingRetained_of_mem_retainedActive_bit_false
          R hx' hbx
      have hyOut :=
        mem_outgoingRetained_of_mem_retainedActive_bit_false
          R hy' hby
      have hzIn :=
        (mem_incomingRetained_iff_retainedBit_true_light
          R i z).2 hbz
      exact
        supportTwo_two_outgoing_one_incoming_labels_oneStep
          hp hcap hn3 hdelta0 hdeltaHalf ht hlam
          Ci hiSecond hiSupport hxy
          (by simpa [R] using hxOut)
          (by simpa [R] using hyOut)
          (by simpa [R] using hzIn)
  | true =>
      have hby : retainedBit R i y = true := by
        rw [← hxyBit, hbx]
      have hbz : retainedBit R i z = false := by
        cases hzbit : retainedBit R i z
        · exact hzbit
        · exact False.elim (hxzBit (by simp [hbx, hzbit]))
      have hxIn :=
        (mem_incomingRetained_iff_retainedBit_true_light
          R i x).2 hbx
      have hyIn :=
        (mem_incomingRetained_iff_retainedBit_true_light
          R i y).2 hby
      have hzOut :=
        mem_outgoingRetained_of_mem_retainedActive_bit_false
          R hz' hbz
      exact
        supportTwo_two_incoming_one_outgoing_labels_oneStep
          hp hcap hn3 hdelta0 hdeltaHalf ht hlam
          Ci hiSecond hiSupport hxy
          (by simpa [R] using hxIn)
          (by simpa [R] using hyIn)
          (by simpa [R] using hzOut)

#print axioms supportTwo_equal_bits_third_opposite_labels_oneStep

end ProjectionOrdered
end JSP000404Research
