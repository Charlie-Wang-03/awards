import JSP000404Research.ThreeWholeCubeInteriorProfileContradictionCore
import JSP000404Research.ProjectionSupportTwoOrientationCloseness
import JSP000404Research.RetainedBitOrientationLight
import Mathlib.Tactic

/-!
# Mixed source-profile contradictions

For a three-whole-cube source v with active owners x,y,z:

* profile 100 is impossible when v, sy, sz are second-layer support-two;
* profile 011 is impossible by relabeling (y,z,x) as a 110 profile.

These two theorems are permutation-ready.  Together with the existing
000 / 111 contradictions they exhaust all eight Boolean source profiles.
-/

namespace JSP000404Research
namespace ProjectionOrdered

open OrderedEdgeColoring

theorem source_100_profile_supportTwo_impossible
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
    (Cfam :
      letI : LinearOrder (ProjectionOrdered V) :=
        projectionLinearOrder hp
      ∀ q : ProjectionOrdered V,
        CentreProjectiveCycle (reindexedPoint_injective hp) q)
    {v sx sy sz : ProjectionOrdered V}
    {x y z : Fin n}
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (hactive :
      letI : LinearOrder (ProjectionOrdered V) :=
        projectionLinearOrder hp
      let R :=
        planarStandardResidualColoring
          hp hcap (by omega : 1 ≤ n)
          hdelta0 (by linarith : delta < 1) ht hlam
      retainedActive R v = {x,y,z})
    (hxPair :
      letI : LinearOrder (ProjectionOrdered V) :=
        projectionLinearOrder hp
      let R :=
        planarStandardResidualColoring
          hp hcap (by omega : 1 ≤ n)
          hdelta0 (by linarith : delta < 1) ht hlam
      WholeCubeQTPair R sx v x)
    (hyPair :
      letI : LinearOrder (ProjectionOrdered V) :=
        projectionLinearOrder hp
      let R :=
        planarStandardResidualColoring
          hp hcap (by omega : 1 ≤ n)
          hdelta0 (by linarith : delta < 1) ht hlam
      WholeCubeQTPair R sy v y)
    (hzPair :
      letI : LinearOrder (ProjectionOrdered V) :=
        projectionLinearOrder hp
      let R :=
        planarStandardResidualColoring
          hp hcap (by omega : 1 ≤ n)
          hdelta0 (by linarith : delta < 1) ht hlam
      WholeCubeQTPair R sz v z)
    (hvSecond :
      letI : LinearOrder (ProjectionOrdered V) :=
        projectionLinearOrder hp
      centreExponent (Cfam v) t = n - 2)
    (hsySecond :
      letI : LinearOrder (ProjectionOrdered V) :=
        projectionLinearOrder hp
      centreExponent (Cfam sy) t = n - 2)
    (hszSecond :
      letI : LinearOrder (ProjectionOrdered V) :=
        projectionLinearOrder hp
      centreExponent (Cfam sz) t = n - 2)
    (hvSupport :
      letI : LinearOrder (ProjectionOrdered V) :=
        projectionLinearOrder hp
      positiveSupport (centreQuotient (Cfam v) t) = 2)
    (hsySupport :
      letI : LinearOrder (ProjectionOrdered V) :=
        projectionLinearOrder hp
      positiveSupport (centreQuotient (Cfam sy) t) = 2)
    (hszSupport :
      letI : LinearOrder (ProjectionOrdered V) :=
        projectionLinearOrder hp
      positiveSupport (centreQuotient (Cfam sz) t) = 2)
    (hxTrue :
      letI : LinearOrder (ProjectionOrdered V) :=
        projectionLinearOrder hp
      let R :=
        planarStandardResidualColoring
          hp hcap (by omega : 1 ≤ n)
          hdelta0 (by linarith : delta < 1) ht hlam
      retainedBit R v x = true)
    (hyFalse :
      letI : LinearOrder (ProjectionOrdered V) :=
        projectionLinearOrder hp
      let R :=
        planarStandardResidualColoring
          hp hcap (by omega : 1 ≤ n)
          hdelta0 (by linarith : delta < 1) ht hlam
      retainedBit R v y = false)
    (hzFalse :
      letI : LinearOrder (ProjectionOrdered V) :=
        projectionLinearOrder hp
      let R :=
        planarStandardResidualColoring
          hp hcap (by omega : 1 ≤ n)
          hdelta0 (by linarith : delta < 1) ht hlam
      retainedBit R v z = false) :
    False := by
  letI : LinearOrder (ProjectionOrdered V) :=
    projectionLinearOrder hp
  have hn1 : 1 ≤ n := by omega
  have hdelta1 : delta < 1 := by linarith
  let R :=
    planarStandardResidualColoring
      hp hcap hn1 hdelta0 hdelta1 ht hlam

  have hactive' : retainedActive R v = {x,y,z} := by
    simpa [R] using hactive
  have hyV : y ∈ retainedActive R v := by rw [hactive']; simp
  have hzV : z ∈ retainedActive R v := by rw [hactive']; simp
  have hxV : x ∈ retainedActive R v := by rw [hactive']; simp

  have hyOut :=
    mem_outgoingRetained_of_mem_retainedActive_bit_false
      R hyV (by simpa [R] using hyFalse)
  have hzOut :=
    mem_outgoingRetained_of_mem_retainedActive_bit_false
      R hzV (by simpa [R] using hzFalse)
  have hxIn :=
    (mem_incomingRetained_iff_retainedBit_true_light R v x).2
      (by simpa [R] using hxTrue)

  have hYZ :=
    supportTwo_two_outgoing_one_incoming_labels_oneStep
      hp hcap hn3 hdelta0 hdeltaHalf ht hlam
      (Cfam v) hvSecond hvSupport hyz
      (by simpa [R] using hyOut)
      (by simpa [R] using hzOut)
      (by simpa [R] using hxIn)

  exact source_second_100_profile_supportTwo_impossible
    hp hcap hn3 hdelta0 hdeltaHalf ht hlam Cfam
    hxy hxz hyz
    hactive hxPair hyPair hzPair
    hsySecond hszSecond hsySupport hszSupport
    hxTrue hyFalse hzFalse hYZ

theorem source_011_profile_supportTwo_impossible
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
    (Cfam :
      letI : LinearOrder (ProjectionOrdered V) :=
        projectionLinearOrder hp
      ∀ q : ProjectionOrdered V,
        CentreProjectiveCycle (reindexedPoint_injective hp) q)
    {v sx sy sz : ProjectionOrdered V}
    {x y z : Fin n}
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (hactive :
      letI : LinearOrder (ProjectionOrdered V) :=
        projectionLinearOrder hp
      let R :=
        planarStandardResidualColoring
          hp hcap (by omega : 1 ≤ n)
          hdelta0 (by linarith : delta < 1) ht hlam
      retainedActive R v = {x,y,z})
    (hxPair :
      letI : LinearOrder (ProjectionOrdered V) :=
        projectionLinearOrder hp
      let R :=
        planarStandardResidualColoring
          hp hcap (by omega : 1 ≤ n)
          hdelta0 (by linarith : delta < 1) ht hlam
      WholeCubeQTPair R sx v x)
    (hyPair :
      letI : LinearOrder (ProjectionOrdered V) :=
        projectionLinearOrder hp
      let R :=
        planarStandardResidualColoring
          hp hcap (by omega : 1 ≤ n)
          hdelta0 (by linarith : delta < 1) ht hlam
      WholeCubeQTPair R sy v y)
    (hzPair :
      letI : LinearOrder (ProjectionOrdered V) :=
        projectionLinearOrder hp
      let R :=
        planarStandardResidualColoring
          hp hcap (by omega : 1 ≤ n)
          hdelta0 (by linarith : delta < 1) ht hlam
      WholeCubeQTPair R sz v z)
    (hvSecond :
      letI : LinearOrder (ProjectionOrdered V) :=
        projectionLinearOrder hp
      centreExponent (Cfam v) t = n - 2)
    (hsySecond :
      letI : LinearOrder (ProjectionOrdered V) :=
        projectionLinearOrder hp
      centreExponent (Cfam sy) t = n - 2)
    (hszSecond :
      letI : LinearOrder (ProjectionOrdered V) :=
        projectionLinearOrder hp
      centreExponent (Cfam sz) t = n - 2)
    (hvSupport :
      letI : LinearOrder (ProjectionOrdered V) :=
        projectionLinearOrder hp
      positiveSupport (centreQuotient (Cfam v) t) = 2)
    (hsySupport :
      letI : LinearOrder (ProjectionOrdered V) :=
        projectionLinearOrder hp
      positiveSupport (centreQuotient (Cfam sy) t) = 2)
    (hszSupport :
      letI : LinearOrder (ProjectionOrdered V) :=
        projectionLinearOrder hp
      positiveSupport (centreQuotient (Cfam sz) t) = 2)
    (hxFalse :
      letI : LinearOrder (ProjectionOrdered V) :=
        projectionLinearOrder hp
      let R :=
        planarStandardResidualColoring
          hp hcap (by omega : 1 ≤ n)
          hdelta0 (by linarith : delta < 1) ht hlam
      retainedBit R v x = false)
    (hyTrue :
      letI : LinearOrder (ProjectionOrdered V) :=
        projectionLinearOrder hp
      let R :=
        planarStandardResidualColoring
          hp hcap (by omega : 1 ≤ n)
          hdelta0 (by linarith : delta < 1) ht hlam
      retainedBit R v y = true)
    (hzTrue :
      letI : LinearOrder (ProjectionOrdered V) :=
        projectionLinearOrder hp
      let R :=
        planarStandardResidualColoring
          hp hcap (by omega : 1 ≤ n)
          hdelta0 (by linarith : delta < 1) ht hlam
      retainedBit R v z = true) :
    False := by
  letI : LinearOrder (ProjectionOrdered V) :=
    projectionLinearOrder hp
  have hn1 : 1 ≤ n := by omega
  have hdelta1 : delta < 1 := by linarith
  let R :=
    planarStandardResidualColoring
      hp hcap hn1 hdelta0 hdelta1 ht hlam

  have hactive' : retainedActive R v = {x,y,z} := by
    simpa [R] using hactive
  have hyV : y ∈ retainedActive R v := by rw [hactive']; simp
  have hzV : z ∈ retainedActive R v := by rw [hactive']; simp
  have hxV : x ∈ retainedActive R v := by rw [hactive']; simp

  have hyIn :=
    (mem_incomingRetained_iff_retainedBit_true_light R v y).2
      (by simpa [R] using hyTrue)
  have hzIn :=
    (mem_incomingRetained_iff_retainedBit_true_light R v z).2
      (by simpa [R] using hzTrue)
  have hxOut :=
    mem_outgoingRetained_of_mem_retainedActive_bit_false
      R hxV (by simpa [R] using hxFalse)

  have hYZ :=
    supportTwo_two_incoming_one_outgoing_labels_oneStep
      hp hcap hn3 hdelta0 hdeltaHalf ht hlam
      (Cfam v) hvSecond hvSupport hyz
      (by simpa [R] using hyIn)
      (by simpa [R] using hzIn)
      (by simpa [R] using hxOut)

  have hactiveRelabeled :
      letI : LinearOrder (ProjectionOrdered V) :=
        projectionLinearOrder hp
      let R' :=
        planarStandardResidualColoring
          hp hcap (by omega : 1 ≤ n)
          hdelta0 (by linarith : delta < 1) ht hlam
      retainedActive R' v = {y,z,x} := by
    letI : LinearOrder (ProjectionOrdered V) :=
      projectionLinearOrder hp
    let R' :=
      planarStandardResidualColoring
        hp hcap (by omega : 1 ≤ n)
        hdelta0 (by linarith : delta < 1) ht hlam
    have hbase : retainedActive R' v = {x,y,z} := by
      simpa [R'] using hactive
    calc
      retainedActive R' v = {x,y,z} := hbase
      _ = {y,z,x} := by
        ext q
        simp only [Finset.mem_insert, Finset.mem_singleton]
        tauto

  exact source_third_110_profile_supportTwo_impossible
    hp hcap hn3 hdelta0 hdeltaHalf ht hlam Cfam
    hyz hxy.symm hxz.symm
    hactiveRelabeled
    hyPair hzPair hxPair
    hsySecond hszSecond hsySupport hszSupport
    hyTrue hzTrue hxFalse hYZ

#print axioms source_100_profile_supportTwo_impossible
#print axioms source_011_profile_supportTwo_impossible

end ProjectionOrdered
end JSP000404Research
