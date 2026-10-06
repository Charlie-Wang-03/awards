import JSP000404Research.ThreeWholeCubeGlobalExtreme
import JSP000404Research.ThreeWholeCubeInteriorProfileContradictionCore
import JSP000404Research.ProjectionSupportTwoOrientationCloseness
import JSP000404Research.RetainedBitOrientationLight
import Mathlib.Tactic

/-!
# Partner-extreme profile contradiction

Fix a three-whole-cube retained-code star with source v and owners x,y,z.

If the x-owner partner sx is the global minimum, all retained bits at sx are
false.  Since sx differs from v only at x, the source profile on x,y,z is
100.  At the support-two source, y and z are both outgoing while x is incoming,
so y,z are one-step close.  The existing 100-profile contradiction applies.

Dually, if sx is the global maximum, the source profile is 011.  Relabeling
(y,z,x) gives the 110-profile, and y,z are both incoming while x is outgoing.
-/

namespace JSP000404Research
namespace ProjectionOrdered

open OrderedEdgeColoring

theorem owner_partner_globalMin_supportTwo_impossible
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
    (hmin :
      letI : LinearOrder (ProjectionOrdered V) :=
        projectionLinearOrder hp
      ∀ w : ProjectionOrdered V, w ≠ sx → sx < w) :
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
  have hxPair' : WholeCubeQTPair R sx v x := by simpa [R] using hxPair
  have hyPair' : WholeCubeQTPair R sy v y := by simpa [R] using hyPair
  have hzPair' : WholeCubeQTPair R sz v z := by simpa [R] using hzPair

  have hxV : x ∈ retainedActive R v := by rw [hactive']; simp
  have hyV : y ∈ retainedActive R v := by rw [hactive']; simp
  have hzV : z ∈ retainedActive R v := by rw [hactive']; simp

  have hstar :=
    threeWholeCubePartners_retainedCode_star
      R hxV hyV hzV hxPair' hyPair' hzPair'

  have hxS : x ∈ retainedActive R sx := by rw [hstar.1.1]; exact hxV
  have hyS : y ∈ retainedActive R sx := by rw [hstar.1.1]; exact hyV
  have hzS : z ∈ retainedActive R sx := by rw [hstar.1.1]; exact hzV

  have hsFalse : AllRetainedBitsFalse R sx :=
    global_min_allRetainedBitsFalse R hmin
  have hxSFalse : retainedBit R sx x = false := hsFalse x hxS
  have hySFalse : retainedBit R sx y = false := hsFalse y hyS
  have hzSFalse : retainedBit R sx z = false := hsFalse z hzS

  have hxVTrue : retainedBit R v x = true := by
    have hflip := hstar.1.2.1
    rw [hxSFalse] at hflip
    cases h : retainedBit R v x with
    | false =>
        simp [h] at hflip
    | true =>
        exact h
  have hyVFalse : retainedBit R v y = false := by
    have heq := hstar.1.2.2 y hyV hxy.symm
    exact heq.symm.trans hySFalse
  have hzVFalse : retainedBit R v z = false := by
    have heq := hstar.1.2.2 z hzV hxz.symm
    exact heq.symm.trans hzSFalse

  have hyOut :=
    mem_outgoingRetained_of_mem_retainedActive_bit_false
      R hyV hyVFalse
  have hzOut :=
    mem_outgoingRetained_of_mem_retainedActive_bit_false
      R hzV hzVFalse
  have hxIn :=
    (mem_incomingRetained_iff_retainedBit_true_light R v x).2 hxVTrue

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
    (by simpa [R] using hxVTrue)
    (by simpa [R] using hyVFalse)
    (by simpa [R] using hzVFalse)
    hYZ

theorem owner_partner_globalMax_supportTwo_impossible
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
    (hmax :
      letI : LinearOrder (ProjectionOrdered V) :=
        projectionLinearOrder hp
      ∀ w : ProjectionOrdered V, w ≠ sx → w < sx) :
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
  have hxPair' : WholeCubeQTPair R sx v x := by simpa [R] using hxPair
  have hyPair' : WholeCubeQTPair R sy v y := by simpa [R] using hyPair
  have hzPair' : WholeCubeQTPair R sz v z := by simpa [R] using hzPair

  have hxV : x ∈ retainedActive R v := by rw [hactive']; simp
  have hyV : y ∈ retainedActive R v := by rw [hactive']; simp
  have hzV : z ∈ retainedActive R v := by rw [hactive']; simp

  have hstar :=
    threeWholeCubePartners_retainedCode_star
      R hxV hyV hzV hxPair' hyPair' hzPair'

  have hxS : x ∈ retainedActive R sx := by rw [hstar.1.1]; exact hxV
  have hyS : y ∈ retainedActive R sx := by rw [hstar.1.1]; exact hyV
  have hzS : z ∈ retainedActive R sx := by rw [hstar.1.1]; exact hzV

  have hsTrue : AllRetainedBitsTrue R sx :=
    global_max_allRetainedBitsTrue R hmax
  have hxSTrue : retainedBit R sx x = true := hsTrue x hxS
  have hySTrue : retainedBit R sx y = true := hsTrue y hyS
  have hzSTrue : retainedBit R sx z = true := hsTrue z hzS

  have hxVFalse : retainedBit R v x = false := by
    have hflip := hstar.1.2.1
    rw [hxSTrue] at hflip
    cases h : retainedBit R v x with
    | false =>
        exact h
    | true =>
        simp [h] at hflip
  have hyVTrue : retainedBit R v y = true := by
    have heq := hstar.1.2.2 y hyV hxy.symm
    exact heq.symm.trans hySTrue
  have hzVTrue : retainedBit R v z = true := by
    have heq := hstar.1.2.2 z hzV hxz.symm
    exact heq.symm.trans hzSTrue

  have hyIn :=
    (mem_incomingRetained_iff_retainedBit_true_light R v y).2 hyVTrue
  have hzIn :=
    (mem_incomingRetained_iff_retainedBit_true_light R v z).2 hzVTrue
  have hxOut :=
    mem_outgoingRetained_of_mem_retainedActive_bit_false
      R hxV hxVFalse

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
    (by simpa [R] using hyVTrue)
    (by simpa [R] using hzVTrue)
    (by simpa [R] using hxVFalse)
    hYZ

#print axioms owner_partner_globalMin_supportTwo_impossible
#print axioms owner_partner_globalMax_supportTwo_impossible

end ProjectionOrdered
end JSP000404Research
