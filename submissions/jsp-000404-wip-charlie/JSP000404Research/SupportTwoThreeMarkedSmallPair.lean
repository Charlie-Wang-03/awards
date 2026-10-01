import JSP000404Research.SupportTwoThreeMarkedArcs
import JSP000404Research.CyclicEdgeRotation
import Mathlib.Tactic

/-!
# Small marked pair at a support-two second-layer centre

First prove the geometric statement assuming the cyclic ray list has already
been written with three marked rays in cyclic order.
-/

namespace JSP000404Research

theorem supportTwo_three_marked_small_pair_of_cyclic_decomposition
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane}
    (hp : Function.Injective p)
    (hcap : AngleCap p lam)
    {lam t delta : ℝ} {n : ℕ}
    (hn3 : 3 ≤ n)
    (hdelta0 : 0 ≤ delta)
    (hdeltaHalf : delta < (1 : ℝ) / 2)
    (ht : t = (n : ℝ) + delta)
    (hlam : lam = Real.pi / t)
    {i : V}
    (C : CentreProjectiveCycle hp i)
    (hexp : centreExponent C t = n - 2)
    (hsupport :
      positiveSupport (centreQuotient C t) = 2)
    (a b c : OtherVertex i)
    (X Y Z : List (OtherVertex i))
    (hrays :
      C.rays = a :: (X ++ b :: Y ++ c :: Z)) :
    EuclideanGeometry.angle (p a.1) (p i) (p b.1)
        ≤ delta * lam
    ∨ EuclideanGeometry.angle (p b.1) (p i) (p c.1)
        ≤ delta * lam
    ∨ EuclideanGeometry.angle (p c.1) (p i) (p a.1)
        ≤ delta * lam := by
  let qs := quotientList t C.gaps
  let A₁ :=
    consecutiveRayAngles (p := p) i a (X ++ [b])
  let A₂ :=
    consecutiveRayAngles (p := p) i b (Y ++ [c])
  let A₃ :=
    consecutiveRayAngles (p := p) i c (Z ++ [a])

  have hangleSplit :
      cyclicRayAngles (p := p) i a
          (X ++ b :: Y ++ c :: Z)
        =
      A₁ ++ A₂ ++ A₃ := by
    dsimp [A₁,A₂,A₃]
    exact cyclicRayAngles_three_marked_split
      (p := p) i a b c X Y Z

  have hqLen :
      qs.length = C.rays.length := by
    dsimp [qs]
    rw [quotientList_length, C.gaps_length]

  have hALen :
      (A₁ ++ A₂ ++ A₃).length = C.rays.length := by
    rw [← hangleSplit]
    rw [cyclicRayAngles_length]
    simpa [hrays]

  have hlen :
      qs.length = (A₁ ++ A₂ ++ A₃).length := by
    rw [hqLen,hALen]

  have hsupportList :
      listPositiveCount qs = 2 := by
    dsimp [qs]
    rw [← centreQuotient_ofFn C t]
    rw [listPositiveCount_ofFn_eq_positiveSupport]
    exact hsupport

  have hdelta1 : delta < 1 := by
    linarith
  have hmass0 :
      listZeroAngleMass
          qs
          (cyclicRayAngles (p := p) i a
            (X ++ b :: Y ++ c :: Z))
        ≤ delta * lam := by
    dsimp [qs]
    exact centre_zeroAngleMass_le_delta_lam
      hp hcap hn3 hdelta0 hdelta1 ht hlam
      i C hexp hsupport
      a (X ++ b :: Y ++ c :: Z) hrays
  have hmass :
      listZeroAngleMass qs (A₁ ++ A₂ ++ A₃)
        ≤ delta * lam := by
    rw [← hangleSplit]
    exact hmass0

  have hA0 :
      ∀ A ∈ A₁ ++ A₂ ++ A₃, 0 ≤ A := by
    intro A hA
    apply all_cyclicRayAngles_nonneg
      (p := p) i a (X ++ b :: Y ++ c :: Z)
    rw [hangleSplit]
    exact hA

  have hpaths :=
    three_marked_path_endpoint_bounds
      (p := p) i a b c X Y Z

  exact aligned_three_angle_blocks_support_two_small_pair
    (p := p)
    i a.1 b.1 c.1
    qs A₁ A₂ A₃
    hlen hsupportList hA0 hmass
    hpaths.1 hpaths.2.1 hpaths.2.2

#print axioms supportTwo_three_marked_small_pair_of_cyclic_decomposition

end JSP000404Research
