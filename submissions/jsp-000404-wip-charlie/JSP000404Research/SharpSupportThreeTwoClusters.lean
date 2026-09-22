import JSP000404Research.SharpPinnedSupportThreeShape
import JSP000404Research.SupportThreeZeroAngleBlocks
import Mathlib.Tactic

/-!
# Two narrow zero-angle blocks for support-three around a sharp centre

The pinned support-three shape has

  quotients = qFirst :: qmid ++ [qLast]

with qFirst,qLast positive and positiveCount(qmid)=1.

Split qmid at its unique positive quotient.  The corresponding middle actual
angle list splits at the same index.  Since the two end quotients and the
hidden middle quotient are positive, the total zero-angle mass is exactly the
sum of the two remaining angle blocks.

The full-quotient remainder budget therefore gives

  leftAngles.sum + rightAngles.sum <= delta*lambda.
-/

namespace JSP000404Research

open Real

theorem exists_sharp_support_three_two_zero_angle_blocks
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane}
    (hp : Function.Injective p)
    (hcap : AngleCap p lam)
    {lam t delta : ℝ} {n : ℕ}
    (hn : 4 ≤ n)
    (hdelta0 : 0 ≤ delta)
    (hdeltaHalf : delta < (1 : ℝ) / 2)
    (ht : t = (n : ℝ) + delta)
    (hlam : lam = Real.pi / t)
    {s i : V}
    (hsi : s ≠ i)
    (hs : SharpAt p delta lam s)
    (C : CentreProjectiveCycle hp i)
    (hexp : centreExponent C t = n - 3)
    (hsupport :
      positiveSupport (centreQuotient C t) = 3) :
    ∃ first0 : OtherVertex i,
      ∃ rest0 : List (OtherVertex i),
      ∃ k : ℕ,
      ∃ r : OtherVertex i,
      ∃ rest : List (OtherVertex i),
      ∃ qFirst qLast : ℕ,
      ∃ leftQ rightQ : List ℕ,
      ∃ qHidden : ℕ,
      ∃ leftA rightA : List ℝ,
      ∃ AHidden : ℝ,
        C.rays = first0 :: rest0 ∧
        C.rays.rotate k =
          (⟨s, hsi⟩ : OtherVertex i) :: r :: rest ∧
        (quotientList t C.gaps).rotate k =
          qFirst :: (leftQ ++ qHidden :: rightQ) ++ [qLast] ∧
        1 ≤ qFirst ∧
        1 ≤ qLast ∧
        qHidden ≠ 0 ∧
        (consecutiveRayAngles (p := p) i r rest) =
          leftA ++ AHidden :: rightA ∧
        leftQ.length = leftA.length ∧
        rightQ.length = rightA.length ∧
        (∀ q ∈ leftQ, q = 0) ∧
        (∀ q ∈ rightQ, q = 0) ∧
        leftA.sum + rightA.sum ≤ delta * lam := by
  obtain ⟨first0, rest0, k, r, rest,
      qFirst, qLast, qmid,
      hrays0, hrotRays, hqRot,
      hqFirst, hqLast, hmidCount, hmidLen,
      hmassRot, hangleRot⟩ :=
    exists_sharp_pinned_support_three_shape
      hp hcap hn hdelta0 hdeltaHalf ht hlam
      hsi hs C hexp hsupport

  let Amid : List ℝ :=
    consecutiveRayAngles (p := p) i r rest
  have hmidLen' : qmid.length = Amid.length := by
    simpa [Amid] using hmidLen

  obtain ⟨leftQ, rightQ, qHidden,
      leftA, rightA, AHidden,
      hqmidSplit, hAmidSplit, hqHidden,
      hleftLen, hrightLen,
      hleftZero, hrightZero, hmidMassEq⟩ :=
    exists_two_zero_angle_blocks_of_positiveCount_one
      qmid Amid hmidCount hmidLen'

  let AFirst : ℝ :=
    EuclideanGeometry.angle (p s) (p i) (p r.1)
  let lastRay : OtherVertex i :=
    (r :: rest).getLastD r
  let ALast : ℝ :=
    EuclideanGeometry.angle (p lastRay.1) (p i) (p s)

  have hcycShape :
      cyclicRayAngles (p := p) i
          (⟨s, hsi⟩ : OtherVertex i) (r :: rest)
        =
      AFirst :: (Amid ++ [ALast]) := by
    simp [cyclicRayAngles, consecutiveRayAngles,
      AFirst, Amid, ALast, lastRay]

  have htotalEqMiddle :
      listZeroAngleMass
          ((quotientList t C.gaps).rotate k)
          ((cyclicRayAngles (p := p) i first0 rest0).rotate k)
        =
      listZeroAngleMass qmid Amid := by
    rw [hqRot, hangleRot, hcycShape]
    exact listZeroAngleMass_positive_ends_eq_middle
      qFirst qLast qmid AFirst ALast Amid
      (by omega) (by omega) hmidLen'

  have hmiddleBound :
      listZeroAngleMass qmid Amid ≤ delta * lam := by
    rw [← htotalEqMiddle]
    exact hmassRot

  have hblocks :
      leftA.sum + rightA.sum ≤ delta * lam := by
    rw [← hmidMassEq]
    exact hmiddleBound

  refine ⟨first0, rest0, k, r, rest,
    qFirst, qLast,
    leftQ, rightQ, qHidden,
    leftA, rightA, AHidden,
    hrays0, hrotRays, ?_,
    hqFirst, hqLast, hqHidden,
    ?_, hleftLen, hrightLen,
    hleftZero, hrightZero, hblocks⟩
  · rw [hqRot, hqmidSplit]
  · simpa [Amid] using hAmidSplit

#print axioms exists_sharp_support_three_two_zero_angle_blocks

end JSP000404Research
