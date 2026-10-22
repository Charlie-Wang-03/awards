import JSP000404Research.SixPointNFourUnconditionalSameSignSlot
import JSP000404Research.SixPointNFourPhaseCover
import Mathlib.Tactic

/-!
# Direct n=4 phase-cover contradiction without all-three-transition classification

Unconditional same-sign slot existence at the ten-unit equality terminal
supplies an unusable concrete unit gap immediately. The existing n=4
nine-usable-slot phase-cover inequality then gives the contradiction.

Unlike the previous proof route, no all-five-minima three-transition
classification, nor any exact-angle witness, is necessary.

The phase-cover lower bound and the fact that a same-sign slot is unusable
for the chosen obstruction predicate remain explicit hypotheses; they
have NOT been deduced unconditionally from AngleCap.
-/

namespace JSP000404Research

open scoped BigOperators

theorem six_point_n_four_equality_no_transition_only_phase_cover_direct
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane}
    (hp : Function.Injective p)
    {lam t delta : ℝ}
    (hcap : AngleCap p lam)
    (hdelta0 : 0 ≤ delta)
    (hdeltaHalf : delta < (1 : ℝ) / 2)
    (ht : t = (4 : ℝ) + delta)
    (hlam : lam = Real.pi / t)
    (C : ∀ i : V, CentreProjectiveCycle hp i)
    (hcard : Fintype.card V = 6)
    (top : V)
    (hTop : centreExponent (C top) t = 3)
    (hMin : ∀ i : V, i ≠ top →
      centreExponent (C i) t = 1)
    (hunitTotal :
      (∑ i : V, unitSupport (centreQuotient (C i) t)) = 10)
    (A : GlobalUnitGapSlot C t → ℝ → Prop)
    (S : Finset (GlobalUnitGapSlot C t))
    (hSameUnusable :
      ∀ u : GlobalUnitGapSlot C t,
        GlobalUnitGapSameSign C t u →
        ∀ x : ℝ, ¬ A u x)
    (hcoverLower :
      ∀ T : Finset (GlobalUnitGapSlot C t), T ⊆ S →
        PredicateCovers A T →
        (4 : ℝ) + delta ≤ (T.card : ℝ) * delta) :
    ¬ PredicateCovers A S := by
  obtain ⟨u, hsame⟩ :=
    six_point_n_four_equality_exists_global_sameSign_unit_slot
      hp hcap hdelta0 hdeltaHalf ht hlam
      C hcard top hTop hMin hunitTotal
  exact
    no_six_point_n_four_globalUnitGapSlot_cover_of_unusable
      C hdelta0 hdeltaHalf ht hcard top hTop hMin
      A S u (hSameUnusable u hsame) hcoverLower

#print axioms six_point_n_four_equality_no_transition_only_phase_cover_direct

end JSP000404Research
