import JSP000404Research.PlanarBridgeSoftStrictDyadicGap
import JSP000404Research.ResidualStrictShellSoftMassLedger
import Mathlib.Tactic

/-!
# Actual planar AngleCap: exact rigid shell / outgoing soft ledger

Specialize the exact abstract oriented singleton-plus-soft shell ledger
to the genuine planar standard residual colouring, with the true
centre projective cycles as target exponents.

Every strict-descent terminal rigid carrier q=(a,v) satisfies:

  2^centreExponent(a) - 2^centreExponent(v)
    = singleton words in (Q_a \ Q_v)
      + SUM_(soft residual r with lower(r)=a)
          2^card(commonRetainedInactive(r)).

No extra abstract one-layer assumption is postulated: the pinned
AngleCap theorem proves it for the actual planar objects.

All terms on the right count already-COVERED words. This is a strict
structural localization, NOT the missing true-hole/net-surplus payment
and NOT a complete JSP-000404 proof.
-/

namespace JSP000404Research
namespace ProjectionOrdered

open OrderedEdgeColoring
open DirectionData

theorem planar_strict_shell_singleton_soft_local_mass_ledger
    {V : Type*} [Fintype V] {p : V → Plane}
    (hp : Function.Injective p)
    {lam t delta : ℝ} {n : ℕ}
    (hcap : AngleCap p lam)
    (hn : 1 ≤ n)
    (hdelta0 : 0 ≤ delta)
    (hdeltaHalf : delta < (1 : ℝ) / 2)
    (ht : t = (n : ℝ) + delta)
    (hlam : lam = Real.pi / t)
    (cycles :
      letI : LinearOrder (ProjectionOrdered V) :=
        projectionLinearOrder hp
      ∀ i : ProjectionOrdered V,
        CentreProjectiveCycle (reindexedPoint_injective hp) i) :
    letI : LinearOrder (ProjectionOrdered V) :=
      projectionLinearOrder hp
    let htpos : 0 < t := by
      rw [ht]
      have hnr : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
      linarith
    let hwidth : t < (n : ℝ) + 1 := by rw [ht]; linarith
    let D := genericDirectionData_sendov hp hcap htpos hlam
    let B := standardResidualColoring D n (by exact_mod_cast hwidth)
    let k : ProjectionOrdered V → ℕ :=
      fun i => centreExponent (cycles i) t
    ∀ q ∈ netStrictDescentRigidCarriers B k,
      ((retainedCompletionWords B q.1 \
          retainedCompletionWords B q.2) ∩
        singletonCompletionWords B).card +
        (∑ r ∈ strictShellOutgoingSoftCarriers B q,
          2 ^ (commonRetainedInactive B r.1 r.2).card) =
      2 ^ k q.1 - 2 ^ k q.2 := by
  classical
  letI : LinearOrder (ProjectionOrdered V) := projectionLinearOrder hp
  have htpos : 0 < t := by
    rw [ht]
    have hnr : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    linarith
  have hwidth : t < (n : ℝ) + 1 := by
    rw [ht]
    linarith
  have hdelta1 : delta < 1 := by linarith
  let D := genericDirectionData_sendov hp hcap htpos hlam
  let B : OrderedEdgeColoring (ProjectionOrdered V) (n + 1) :=
    standardResidualColoring D n (by exact_mod_cast hwidth)
  let k : ProjectionOrdered V → ℕ :=
    fun i => centreExponent (cycles i) t
  have hexp : ∀ i : ProjectionOrdered V, k i ≤ n := by
    intro i
    exact Nat.le_of_lt
      (centreExponent_lt_n (cycles i) n delta t
        hn hdelta0 hdelta1 ht)
  have honeLoss :
      ∀ i : ProjectionOrdered V,
        (active B i).card ≤ n - k i + 1 := by
    intro i
    exact planarStandardResidual_active_card_le_oneLayer
      hp hcap hn hdelta0 hdelta1 ht hlam i (cycles i)
  change ∀ q ∈ netStrictDescentRigidCarriers B k,
      ((retainedCompletionWords B q.1 \
          retainedCompletionWords B q.2) ∩
        singletonCompletionWords B).card +
        (∑ r ∈ strictShellOutgoingSoftCarriers B q,
          2 ^ (commonRetainedInactive B r.1 r.2).card) =
      2 ^ k q.1 - 2 ^ k q.2
  intro q hq
  exact strict_shell_singleton_add_outgoing_soft_mass_eq_target_gap
    B k hexp honeLoss hq

#print axioms planar_strict_shell_singleton_soft_local_mass_ledger

end ProjectionOrdered
end JSP000404Research
