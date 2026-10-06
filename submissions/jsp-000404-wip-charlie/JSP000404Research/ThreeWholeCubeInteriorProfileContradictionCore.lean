import JSP000404Research.ProjectionSupportTwoOrientationCloseness
import JSP000404Research.RetainedBitOrientationLight
import JSP000404Research.ThreeWholeCubeRetainedCodeStar
import JSP000404Research.FourCycleOwnerChoiceRigidity
import Mathlib.Tactic

/-!
# Interior-source 100 / 110 profile contradiction

The final two staircase profiles are incompatible with support-two geometry.

Source = second point, profile 100:
* the y-partner has code 110, so x,y are incoming and z is outgoing;
* the z-partner has code 101, so x,z are incoming and y is outgoing.
Support-two therefore forces x~y and x~z one-step close.
The staircase already gives y~z.  Three distinct natural labels cannot be
pairwise one-step close.

Source = third point, profile 110:
* the x-partner has code 010, so x,z are outgoing and y is incoming;
* the y-partner has code 100, so y,z are outgoing and x is incoming.
Support-two forces x~z and y~z, while the staircase gives x~y.

Thus both remaining interior-source profiles are impossible.
-/

namespace JSP000404Research
namespace ProjectionOrdered

open OrderedEdgeColoring

private theorem fin_val_ne
    {n : ℕ} {x y : Fin n}
    (hxy : x ≠ y) :
    x.val ≠ y.val := by
  intro h
  apply hxy
  exact Fin.ext h

theorem source_second_100_profile_supportTwo_impossible
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
      ∀ q : ProjectionOrdered V,
        CentreProjectiveCycle (reindexedPoint_injective hp) q)
    {a b c d : ProjectionOrdered V}
    {x y z : Fin n}
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (hactive :
      letI : LinearOrder (ProjectionOrdered V) :=
        projectionLinearOrder hp
      let R :=
        planarStandardResidualColoring
          hp hcap (by omega : 1 ≤ n)
          hdelta0 (by linarith : delta < 1) ht hlam
      retainedActive R b = {x,y,z})
    (ha :
      letI : LinearOrder (ProjectionOrdered V) :=
        projectionLinearOrder hp
      let R :=
        planarStandardResidualColoring
          hp hcap (by omega : 1 ≤ n)
          hdelta0 (by linarith : delta < 1) ht hlam
      WholeCubeQTPair R a b x)
    (hc :
      letI : LinearOrder (ProjectionOrdered V) :=
        projectionLinearOrder hp
      let R :=
        planarStandardResidualColoring
          hp hcap (by omega : 1 ≤ n)
          hdelta0 (by linarith : delta < 1) ht hlam
      WholeCubeQTPair R c b y)
    (hd :
      letI : LinearOrder (ProjectionOrdered V) :=
        projectionLinearOrder hp
      let R :=
        planarStandardResidualColoring
          hp hcap (by omega : 1 ≤ n)
          hdelta0 (by linarith : delta < 1) ht hlam
      WholeCubeQTPair R d b z)
    (hcSecond : centreExponent (Cfam c) t = n - 2)
    (hdSecond : centreExponent (Cfam d) t = n - 2)
    (hcSupport : positiveSupport (centreQuotient (Cfam c) t) = 2)
    (hdSupport : positiveSupport (centreQuotient (Cfam d) t) = 2)
    (hxBTrue :
      letI : LinearOrder (ProjectionOrdered V) :=
        projectionLinearOrder hp
      let R :=
        planarStandardResidualColoring
          hp hcap (by omega : 1 ≤ n)
          hdelta0 (by linarith : delta < 1) ht hlam
      retainedBit R b x = true)
    (hyBFalse :
      letI : LinearOrder (ProjectionOrdered V) :=
        projectionLinearOrder hp
      let R :=
        planarStandardResidualColoring
          hp hcap (by omega : 1 ≤ n)
          hdelta0 (by linarith : delta < 1) ht hlam
      retainedBit R b y = false)
    (hzBFalse :
      letI : LinearOrder (ProjectionOrdered V) :=
        projectionLinearOrder hp
      let R :=
        planarStandardResidualColoring
          hp hcap (by omega : 1 ≤ n)
          hdelta0 (by linarith : delta < 1) ht hlam
      retainedBit R b z = false)
    (hYZ : NatOneStepClose y.val z.val) :
    False := by
  letI : LinearOrder (ProjectionOrdered V) :=
    projectionLinearOrder hp
  have hn1 : 1 ≤ n := by omega
  have hdelta1 : delta < 1 := by linarith
  let R :=
    planarStandardResidualColoring
      hp hcap hn1 hdelta0 hdelta1 ht hlam

  have hactive' : retainedActive R b = {x,y,z} := by
    simpa [R] using hactive
  have ha' : WholeCubeQTPair R a b x := by simpa [R] using ha
  have hc' : WholeCubeQTPair R c b y := by simpa [R] using hc
  have hd' : WholeCubeQTPair R d b z := by simpa [R] using hd
  have hxBTrue' : retainedBit R b x = true := by simpa [R] using hxBTrue
  have hyBFalse' : retainedBit R b y = false := by simpa [R] using hyBFalse
  have hzBFalse' : retainedBit R b z = false := by simpa [R] using hzBFalse

  have hxB : x ∈ retainedActive R b := by rw [hactive']; simp
  have hyB : y ∈ retainedActive R b := by rw [hactive']; simp
  have hzB : z ∈ retainedActive R b := by rw [hactive']; simp

  have hstar :=
    threeWholeCubePartners_retainedCode_star
      R hxB hyB hzB ha' hc' hd'

  have hxC : x ∈ retainedActive R c := by
    rw [hstar.2.1.1]
    exact hxB
  have hyC : y ∈ retainedActive R c := by
    rw [hstar.2.1.1]
    exact hyB
  have hzC : z ∈ retainedActive R c := by
    rw [hstar.2.1.1]
    exact hzB
  have hxD : x ∈ retainedActive R d := by
    rw [hstar.2.2.1]
    exact hxB
  have hyD : y ∈ retainedActive R d := by
    rw [hstar.2.2.1]
    exact hyB
  have hzD : z ∈ retainedActive R d := by
    rw [hstar.2.2.1]
    exact hzB

  have hxCTrue : retainedBit R c x = true := by
    exact (hstar.2.1.2.2 x hxB hxy).trans hxBTrue'
  have hyCTrue : retainedBit R c y = true := by
    have hflip := hstar.2.1.2.1
    rw [hyBFalse'] at hflip
    simpa using hflip
  have hzCFalse : retainedBit R c z = false := by
    exact (hstar.2.1.2.2 z hzB hyz.symm).trans hzBFalse'

  have hxDTrue : retainedBit R d x = true := by
    exact (hstar.2.2.2.2 x hxB hxz).trans hxBTrue'
  have hyDFalse : retainedBit R d y = false := by
    exact (hstar.2.2.2.2 y hyB hyz).trans hyBFalse'
  have hzDTrue : retainedBit R d z = true := by
    have hflip := hstar.2.2.2.1
    rw [hzBFalse'] at hflip
    simpa using hflip

  have hxCIn :=
    (mem_incomingRetained_iff_retainedBit_true_light R c x).2 hxCTrue
  have hyCIn :=
    (mem_incomingRetained_iff_retainedBit_true_light R c y).2 hyCTrue
  have hzCOut :=
    mem_outgoingRetained_of_mem_retainedActive_bit_false
      R hzC hzCFalse

  have hxDIn :=
    (mem_incomingRetained_iff_retainedBit_true_light R d x).2 hxDTrue
  have hzDIn :=
    (mem_incomingRetained_iff_retainedBit_true_light R d z).2 hzDTrue
  have hyDOut :=
    mem_outgoingRetained_of_mem_retainedActive_bit_false
      R hyD hyDFalse

  have hXY :=
    supportTwo_two_incoming_one_outgoing_labels_oneStep
      hp hcap hn3 hdelta0 hdeltaHalf ht hlam
      (Cfam c) hcSecond hcSupport hxy
      (by simpa [R] using hxCIn)
      (by simpa [R] using hyCIn)
      (by simpa [R] using hzCOut)

  have hXZ :=
    supportTwo_two_incoming_one_outgoing_labels_oneStep
      hp hcap hn3 hdelta0 hdeltaHalf ht hlam
      (Cfam d) hdSecond hdSupport hxz
      (by simpa [R] using hxDIn)
      (by simpa [R] using hzDIn)
      (by simpa [R] using hyDOut)

  exact
    three_distinct_pairwise_oneStep_impossible
      x.val y.val z.val
      (fin_val_ne hxy) (fin_val_ne hxz) (fin_val_ne hyz)
      hXY hXZ hYZ

theorem source_third_110_profile_supportTwo_impossible
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
      ∀ q : ProjectionOrdered V,
        CentreProjectiveCycle (reindexedPoint_injective hp) q)
    {a b c d : ProjectionOrdered V}
    {x y z : Fin n}
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (hactive :
      letI : LinearOrder (ProjectionOrdered V) :=
        projectionLinearOrder hp
      let R :=
        planarStandardResidualColoring
          hp hcap (by omega : 1 ≤ n)
          hdelta0 (by linarith : delta < 1) ht hlam
      retainedActive R c = {x,y,z})
    (ha :
      letI : LinearOrder (ProjectionOrdered V) :=
        projectionLinearOrder hp
      let R :=
        planarStandardResidualColoring
          hp hcap (by omega : 1 ≤ n)
          hdelta0 (by linarith : delta < 1) ht hlam
      WholeCubeQTPair R a c x)
    (hb :
      letI : LinearOrder (ProjectionOrdered V) :=
        projectionLinearOrder hp
      let R :=
        planarStandardResidualColoring
          hp hcap (by omega : 1 ≤ n)
          hdelta0 (by linarith : delta < 1) ht hlam
      WholeCubeQTPair R b c y)
    (hd :
      letI : LinearOrder (ProjectionOrdered V) :=
        projectionLinearOrder hp
      let R :=
        planarStandardResidualColoring
          hp hcap (by omega : 1 ≤ n)
          hdelta0 (by linarith : delta < 1) ht hlam
      WholeCubeQTPair R d c z)
    (haSecond : centreExponent (Cfam a) t = n - 2)
    (hbSecond : centreExponent (Cfam b) t = n - 2)
    (haSupport : positiveSupport (centreQuotient (Cfam a) t) = 2)
    (hbSupport : positiveSupport (centreQuotient (Cfam b) t) = 2)
    (hxCTrue :
      letI : LinearOrder (ProjectionOrdered V) :=
        projectionLinearOrder hp
      let R :=
        planarStandardResidualColoring
          hp hcap (by omega : 1 ≤ n)
          hdelta0 (by linarith : delta < 1) ht hlam
      retainedBit R c x = true)
    (hyCTrue :
      letI : LinearOrder (ProjectionOrdered V) :=
        projectionLinearOrder hp
      let R :=
        planarStandardResidualColoring
          hp hcap (by omega : 1 ≤ n)
          hdelta0 (by linarith : delta < 1) ht hlam
      retainedBit R c y = true)
    (hzCFalse :
      letI : LinearOrder (ProjectionOrdered V) :=
        projectionLinearOrder hp
      let R :=
        planarStandardResidualColoring
          hp hcap (by omega : 1 ≤ n)
          hdelta0 (by linarith : delta < 1) ht hlam
      retainedBit R c z = false)
    (hXY : NatOneStepClose x.val y.val) :
    False := by
  letI : LinearOrder (ProjectionOrdered V) :=
    projectionLinearOrder hp
  have hn1 : 1 ≤ n := by omega
  have hdelta1 : delta < 1 := by linarith
  let R :=
    planarStandardResidualColoring
      hp hcap hn1 hdelta0 hdelta1 ht hlam

  have hactive' : retainedActive R c = {x,y,z} := by
    simpa [R] using hactive
  have ha' : WholeCubeQTPair R a c x := by simpa [R] using ha
  have hb' : WholeCubeQTPair R b c y := by simpa [R] using hb
  have hd' : WholeCubeQTPair R d c z := by simpa [R] using hd
  have hxCTrue' : retainedBit R c x = true := by simpa [R] using hxCTrue
  have hyCTrue' : retainedBit R c y = true := by simpa [R] using hyCTrue
  have hzCFalse' : retainedBit R c z = false := by simpa [R] using hzCFalse

  have hxC : x ∈ retainedActive R c := by rw [hactive']; simp
  have hyC : y ∈ retainedActive R c := by rw [hactive']; simp
  have hzC : z ∈ retainedActive R c := by rw [hactive']; simp

  have hstar :=
    threeWholeCubePartners_retainedCode_star
      R hxC hyC hzC ha' hb' hd'

  have hxA : x ∈ retainedActive R a := by
    rw [hstar.1.1]
    exact hxC
  have hyA : y ∈ retainedActive R a := by
    rw [hstar.1.1]
    exact hyC
  have hzA : z ∈ retainedActive R a := by
    rw [hstar.1.1]
    exact hzC
  have hxB : x ∈ retainedActive R b := by
    rw [hstar.2.1.1]
    exact hxC
  have hyB : y ∈ retainedActive R b := by
    rw [hstar.2.1.1]
    exact hyC
  have hzB : z ∈ retainedActive R b := by
    rw [hstar.2.1.1]
    exact hzC

  have hxAFalse : retainedBit R a x = false := by
    have hflip := hstar.1.2.1
    rw [hxCTrue'] at hflip
    simpa using hflip
  have hyATrue : retainedBit R a y = true := by
    exact (hstar.1.2.2 y hyC hxy.symm).trans hyCTrue'
  have hzAFalse : retainedBit R a z = false := by
    exact (hstar.1.2.2 z hzC hxz.symm).trans hzCFalse'

  have hxBTrue : retainedBit R b x = true := by
    exact (hstar.2.1.2.2 x hxC hxy).trans hxCTrue'
  have hyBFalse : retainedBit R b y = false := by
    have hflip := hstar.2.1.2.1
    rw [hyCTrue'] at hflip
    simpa using hflip
  have hzBFalse : retainedBit R b z = false := by
    exact (hstar.2.1.2.2 z hzC hyz.symm).trans hzCFalse'

  have hxAOut :=
    mem_outgoingRetained_of_mem_retainedActive_bit_false
      R hxA hxAFalse
  have hzAOut :=
    mem_outgoingRetained_of_mem_retainedActive_bit_false
      R hzA hzAFalse
  have hyAIn :=
    (mem_incomingRetained_iff_retainedBit_true_light R a y).2 hyATrue

  have hyBOut :=
    mem_outgoingRetained_of_mem_retainedActive_bit_false
      R hyB hyBFalse
  have hzBOut :=
    mem_outgoingRetained_of_mem_retainedActive_bit_false
      R hzB hzBFalse
  have hxBIn :=
    (mem_incomingRetained_iff_retainedBit_true_light R b x).2 hxBTrue

  have hXZ :=
    supportTwo_two_outgoing_one_incoming_labels_oneStep
      hp hcap hn3 hdelta0 hdeltaHalf ht hlam
      (Cfam a) haSecond haSupport hxz
      (by simpa [R] using hxAOut)
      (by simpa [R] using hzAOut)
      (by simpa [R] using hyAIn)

  have hYZ :=
    supportTwo_two_outgoing_one_incoming_labels_oneStep
      hp hcap hn3 hdelta0 hdeltaHalf ht hlam
      (Cfam b) hbSecond hbSupport hyz
      (by simpa [R] using hyBOut)
      (by simpa [R] using hzBOut)
      (by simpa [R] using hxBIn)

  exact
    three_distinct_pairwise_oneStep_impossible
      x.val y.val z.val
      (fin_val_ne hxy) (fin_val_ne hxz) (fin_val_ne hyz)
      hXY hXZ hYZ

#print axioms source_second_100_profile_supportTwo_impossible
#print axioms source_third_110_profile_supportTwo_impossible

end ProjectionOrdered
end JSP000404Research
