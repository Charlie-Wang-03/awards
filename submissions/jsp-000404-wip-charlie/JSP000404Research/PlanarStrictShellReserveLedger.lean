import JSP000404Research.PlanarBridgeSoftStrictDyadicGap
import JSP000404Research.ResidualStrictShellGlobalReserveLedger
import Mathlib.Tactic

/-!
# Actual planar AngleCap: exact global strict shell three-way reservation

The genuine planar standard residual colouring and true centre projective
cycle target exponents satisfy the verified abstract one-layer budgets.

Every strict lower shell belongs to exactly one of these disjoint
categories: singleton-covered words, potential forward/reverse bridge
soft words, and nonbridge soft-overlap words. In the planar model:

  singletonShellMass + bridgeSoftMass + nonBridgeShellSoftMass
    = SUM_strict (2^k(lower) - 2^k(upper)).

The latter is the already-COVERED strict dimensional descent gap,
NOT a true Boolean hole or nonreserved dyadic profile surplus.
There is no extra abstract budget assumption and no admitted proof.
-/

namespace JSP000404Research
namespace ProjectionOrdered

open OrderedEdgeColoring
open DirectionData

theorem planar_strict_shell_singleton_bridge_nonbridge_exact_ledger
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
    (strictShellSingletonWords B k).card +
      (forwardReverseBridgeSoftWords B k).card +
        (strictShellNonBridgeSoftWords B k).card =
      ∑ q ∈ netStrictDescentRigidCarriers B k,
        (2 ^ k q.1 - 2 ^ k q.2) := by
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
  change (strictShellSingletonWords B k).card +
      (forwardReverseBridgeSoftWords B k).card +
        (strictShellNonBridgeSoftWords B k).card =
      ∑ q ∈ netStrictDescentRigidCarriers B k,
        (2 ^ k q.1 - 2 ^ k q.2)
  exact strict_shell_singleton_bridge_nonbridge_eq_local_gaps
    B k hexp honeLoss

#print axioms planar_strict_shell_singleton_bridge_nonbridge_exact_ledger

end ProjectionOrdered
end JSP000404Research
