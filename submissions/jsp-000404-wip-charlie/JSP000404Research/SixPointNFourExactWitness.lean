import JSP000404Research.SixPointNFourEquality
import JSP000404Research.ExactWitnessCentreBound
import JSP000404Research.ExactWitnessSupportThreeTransition
import Mathlib.Tactic

/-!
# Exact-witness shape in the n=4 six-point equality terminal

The ten-unit-slot equality terminal has one top centre of exponent 3 and five
minimum centres of exponent 1.  Every minimum has quotient support exactly
three and positive multiset {1,1,2}.

The centre of an exact maximum-angle witness cannot be the top centre:
ExactWitnessCentreBound gives exponent at most n-2=2.  Hence it is one of the
five minima.  Therefore its quotient support is exactly three, with two unit
coordinates and one coordinate equal to two.

Combining this with the exact-witness support-three transition dichotomy leaves
only two geometric possibilities:

* the witness centre is strictly exposed and has a one-transition
  decomposition whose transition quotient is one; or
* it has exactly three sign transitions, one of which is the exact unit
  witness transition.
-/

namespace JSP000404Research

/-- In the n=4 six-point equality terminal the exact-witness centre is one of
the five minima, hence has exponent one. -/
theorem six_point_n_four_exactWitness_centre_is_minimum
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane}
    (hp : Function.Injective p)
    (hcap : AngleCap p lam)
    {lam t delta : ℝ}
    (hdelta0 : 0 ≤ delta)
    (hdeltaHalf : delta < (1 : ℝ) / 2)
    (ht : t = (4 : ℝ) + delta)
    (hlam : lam = Real.pi / t)
    (W : ExactAngleWitness p lam)
    (C : ∀ i : V, CentreProjectiveCycle hp i)
    (top : V)
    (hTop : centreExponent (C top) t = 3)
    (hMin :
      ∀ i : V, i ≠ top →
        centreExponent (C i) t = 1) :
    W.b ≠ top ∧
      centreExponent (C W.b) t = 1 := by
  have hWle :
      centreExponent (C W.b) t ≤ 2 := by
    simpa using
      exactWitness_centreExponent_le_n_sub_two
        hp hcap (by norm_num : 3 ≤ 4)
        hdelta0 hdeltaHalf ht hlam W (C W.b)
  have hne : W.b ≠ top := by
    intro h
    subst top
    omega
  exact ⟨hne, hMin W.b hne⟩

/-- Equality of the global ten-slot budget forces the exact-witness centre to
have the full third-layer multiset {1,1,2,0,0}. -/
theorem six_point_n_four_exactWitness_forced_11200
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane}
    (hp : Function.Injective p)
    (hcap : AngleCap p lam)
    {lam t delta : ℝ}
    (hdelta0 : 0 ≤ delta)
    (hdeltaHalf : delta < (1 : ℝ) / 2)
    (ht : t = (4 : ℝ) + delta)
    (hlam : lam = Real.pi / t)
    (W : ExactAngleWitness p lam)
    (C : ∀ i : V, CentreProjectiveCycle hp i)
    (hcard : Fintype.card V = 6)
    (top : V)
    (hTop : centreExponent (C top) t = 3)
    (hMin :
      ∀ i : V, i ≠ top →
        centreExponent (C i) t = 1)
    (hunitTotal :
      (∑ i : V,
        unitSupport (centreQuotient (C i) t)) = 10) :
    unitSupport (centreQuotient (C W.b) t) = 2 ∧
      positiveSupport (centreQuotient (C W.b) t) = 3 ∧
      twoSupport (centreQuotient (C W.b) t) = 1 ∧
      ∀ r,
        centreQuotient (C W.b) t r ≠ 0 →
        centreQuotient (C W.b) t r = 1 ∨
          centreQuotient (C W.b) t r = 2 := by
  have hminW :=
    six_point_n_four_exactWitness_centre_is_minimum
      hp hcap hdelta0 hdeltaHalf ht hlam
      W C top hTop hMin
  exact
    six_point_n_four_unit_budget_equality_forces_11200
      C hdelta0 hdeltaHalf ht hcard
      top hTop hMin hunitTotal
      W.b hminW.1

/-- Final exact-witness dichotomy in the n=4 equality terminal. -/
theorem six_point_n_four_exactWitness_terminal_dichotomy
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane}
    (hp : Function.Injective p)
    (hcap : AngleCap p lam)
    {lam t delta : ℝ}
    (hdelta0 : 0 ≤ delta)
    (hdeltaHalf : delta < (1 : ℝ) / 2)
    (ht : t = (4 : ℝ) + delta)
    (hlam : lam = Real.pi / t)
    (W : ExactAngleWitness p lam)
    (C : ∀ i : V, CentreProjectiveCycle hp i)
    (hcard : Fintype.card V = 6)
    (top : V)
    (hTop : centreExponent (C top) t = 3)
    (hMin :
      ∀ i : V, i ≠ top →
        centreExponent (C i) t = 1)
    (hunitTotal :
      (∑ i : V,
        unitSupport (centreQuotient (C i) t)) = 10) :
    (
      StrictlyExposedAt p W.b ∧
      ∃ first : OtherVertex W.b,
        ∃ rest : List (OtherVertex W.b),
        ∃ pre post : List ℕ,
          (C W.b).rays = first :: rest ∧
          quotientList t (C W.b).gaps = pre ++ 1 :: post ∧
          liftedCentreSignPath hp W.b first rest =
            List.replicate pre.length (raySignAt hp W.b first) ++
              List.replicate (post.length + 1)
                (!raySignAt hp W.b first)
    )
    ∨
    (
      ∃ first : OtherVertex W.b,
        ∃ rest : List (OtherVertex W.b),
          (C W.b).rays = first :: rest ∧
          TransitionQuotientOccurs 1
            (raySignAt hp W.b first)
            (liftedCentreSignPath hp W.b first rest)
            (quotientList t (C W.b).gaps) ∧
          boolTransitionCountFrom
            (raySignAt hp W.b first)
            (liftedCentreSignPath hp W.b first rest) = 3
    ) := by
  have hshape :=
    six_point_n_four_exactWitness_forced_11200
      hp hcap hdelta0 hdeltaHalf ht hlam
      W C hcard top hTop hMin hunitTotal
  exact
    exactWitness_support_three_exposed_unit_transition_or_three
      hp hcap (by norm_num : 3 ≤ 4)
      hdelta0 ht hlam W (C W.b) hshape.2.1

#print axioms six_point_n_four_exactWitness_centre_is_minimum
#print axioms six_point_n_four_exactWitness_forced_11200
#print axioms six_point_n_four_exactWitness_terminal_dichotomy

end JSP000404Research
