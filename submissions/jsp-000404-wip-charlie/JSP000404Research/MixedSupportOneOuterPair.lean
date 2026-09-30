import JSP000404Research.MixedSupportThreeSeparatedPatterns
import JSP000404Research.MixedSupportOneOuterAmplification
import Mathlib.Tactic

/-!
# Two support-one-amplified outer edges in the mixed hard branch

The mixed six-point hard branch contains two non-exposed support-three minima
with enriched middle-hidden patterns.  The support-one minimum is one of the
four non-top rays at each such centre.

The support-one outer-angle lower bound therefore transfers, at both
middle-hidden centres, to at least one of the two positive outer transition
edges:

  (((n-2)-2*delta) * lambda) <= angle(top,i,r)

or

  (((n-2)-2*delta) * lambda) <= angle(d,i,top).

This keeps the two strengthened witnesses simultaneously, rather than
reconstructing them independently downstream.
-/

namespace JSP000404Research

theorem mixed_support_one_has_two_outer_amplified_patterns
    {V : Type*} [LinearOrder V] [Fintype V] [DecidableEq V]
    {p : V → Plane}
    {lam t delta : ℝ} {n : ℕ}
    (hp : Function.Injective p)
    (hcap : AngleCap p lam)
    (C : ∀ i : V, CentreProjectiveCycle hp i)
    (hcard : Fintype.card V = 6)
    (hn5 : 5 ≤ n)
    (hdelta0 : 0 ≤ delta)
    (hdeltaHalf : delta < (1 : ℝ) / 2)
    (ht : t = (n : ℝ) + delta)
    (hlam : lam = Real.pi / t)
    (top a : V)
    (hta : top ≠ a)
    (hTop : centreExponent (C top) t = n - 1)
    (hMin :
      ∀ v : V, v ≠ top →
        centreExponent (C v) t = n - 3)
    (hsupA :
      positiveSupport (centreQuotient (C a) t) = 1)
    (hNoMin :
      SixPointNoCompensatedMinimumDeletion
        C (by rw [hcard]; omega) top t n) :
    ∃ b c : V,
      b ≠ top ∧ c ≠ top ∧
      b ≠ a ∧ c ≠ a ∧ b ≠ c ∧
      positiveSupport (centreQuotient (C b) t) = 3 ∧
      positiveSupport (centreQuotient (C c) t) = 3 ∧
      ∃ Mb :
          MiddleHiddenSeparatedPatternAwayFromTop
            p top b delta lam,
      ∃ Mc :
          MiddleHiddenSeparatedPatternAwayFromTop
            p top c delta lam,
        (
          (((n - 2 : ℕ) : ℝ) - 2 * delta) * lam ≤
              EuclideanGeometry.angle (p top) (p b) (p Mb.r.1)
          ∨
          (((n - 2 : ℕ) : ℝ) - 2 * delta) * lam ≤
              EuclideanGeometry.angle (p Mb.d.1) (p b) (p top)
        )
        ∧
        (
          (((n - 2 : ℕ) : ℝ) - 2 * delta) * lam ≤
              EuclideanGeometry.angle (p top) (p c) (p Mc.r.1)
          ∨
          (((n - 2 : ℕ) : ℝ) - 2 * delta) * lam ≤
              EuclideanGeometry.angle (p Mc.d.1) (p c) (p top)
        ) := by
  obtain ⟨b,c,
      hbTop,hcTop,hbA,hcA,hbc,
      hbSup3,hcSup3,hMb,hMc⟩ :=
    mixed_support_one_has_two_separated_patterns
      hp hcap C hcard hn5 hdelta0 hdeltaHalf
      ht hlam top a hta hTop hMin hsupA hNoMin
  let Mb := Classical.choice hMb
  let Mc := Classical.choice hMc
  have hbOuter :=
    middle_hidden_outer_strengthened_by_support_one
      hp hcap hcard (by omega : 4 ≤ n)
      hdelta0 hdeltaHalf ht hlam
      hbTop hta.symm hbA.symm
      (C top) (C a) hTop (hMin a hta.symm)
      hsupA Mb
  have hcOuter :=
    middle_hidden_outer_strengthened_by_support_one
      hp hcap hcard (by omega : 4 ≤ n)
      hdelta0 hdeltaHalf ht hlam
      hcTop hta.symm hcA.symm
      (C top) (C a) hTop (hMin a hta.symm)
      hsupA Mc
  exact ⟨b,c,
    hbTop,hcTop,hbA,hcA,hbc,
    hbSup3,hcSup3,Mb,Mc,hbOuter,hcOuter⟩

#print axioms mixed_support_one_has_two_outer_amplified_patterns

end JSP000404Research
