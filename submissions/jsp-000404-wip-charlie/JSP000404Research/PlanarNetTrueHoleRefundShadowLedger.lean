import JSP000404Research.PlanarNetNineCentreTwinTradeoff
import JSP000404Research.ResidualNetCollisionTrueHoleRefundShadowLedger
import Mathlib.Tactic

/-!
# True planar AngleCap NET true-hole refund from SOFT shadow incidences

The certified exact net mobile source upper bound can be rewritten
without its distinct COVERED target blocker charge and without
reusing TRUE Boolean holes ALREADY used as actual NET diagonal
first hits. The RHS retains a still-UNPAID multiplicity-indexed
COVERED SOFT-shadow incidence sum.

This theorem is a sharp accounting reduction of the real planar
six-source payment frontier, NOT an unrestricted payment proof.
-/

namespace JSP000404Research
namespace ProjectionOrdered

open OrderedEdgeColoring
open DirectionData

theorem planar_net_mobile_true_hole_refund_shadow_ledger
    {V : Type*} [Fintype V]
    {p : V → Plane}
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
    let hwidth : t < (n : ℝ) + 1 := by
      rw [ht]
      linarith
    let D := genericDirectionData_sendov hp hcap htpos hlam
    let B := standardResidualColoring D n (by exact_mod_cast hwidth)
    let k : ProjectionOrdered V → ℕ :=
      fun i => centreExponent (cycles i) t
    ∃ (hexp : ∀ i : ProjectionOrdered V, k i ≤ n),
      ∃ (honeLoss : ∀ i : ProjectionOrdered V,
        (active B i).card ≤ n - k i + 1),
        (netTransportableHardWords B k).card +
          (netStrictDescentRigidWords B k).card ≤
          (singletonCompletionWords B).card +
          (softOverlapCompletionWords B).card +
          (((Finset.univ : Finset (Fin n → Bool)) \\
              coveredCompletionWords B).card -
            (netCollisionCertifiedTrueHoleDiagonals
              B k hexp honeLoss).card) +
          (∑ s ∈ softOverlapCompletionWords B,
            ((netCollisionCertifiedDiagonalWords B k hexp honeLoss).filter
              (fun d =>
                (Finset.univ.filter (fun i : Fin n => s i ≠ d i)).card = 2)).card) := by
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
  change ∃ (hexp : ∀ i : ProjectionOrdered V, k i ≤ n),
      ∃ (honeLoss : ∀ i : ProjectionOrdered V,
        (active B i).card ≤ n - k i + 1),
        (netTransportableHardWords B k).card +
          (netStrictDescentRigidWords B k).card ≤
          (singletonCompletionWords B).card +
          (softOverlapCompletionWords B).card +
          (((Finset.univ : Finset (Fin n → Bool)) \\
              coveredCompletionWords B).card -
            (netCollisionCertifiedTrueHoleDiagonals
              B k hexp honeLoss).card) +
          (∑ s ∈ softOverlapCompletionWords B,
            ((netCollisionCertifiedDiagonalWords B k hexp honeLoss).filter
              (fun d =>
                (Finset.univ.filter (fun i : Fin n => s i ≠ d i)).card = 2)).card)
  have hstrict : ∀ i : ProjectionOrdered V, k i < n := by
    intro i
    exact centreExponent_lt_n (cycles i) n delta t
      hn hdelta0 hdelta1 ht
  have hexp : ∀ i : ProjectionOrdered V, k i ≤ n :=
    fun i => (hstrict i).le
  have honeLoss :
      ∀ i : ProjectionOrdered V,
        (active B i).card ≤ n - k i + 1 := by
    intro i
    exact planarStandardResidual_active_card_le_oneLayer
      hp hcap hn hdelta0 hdelta1 ht hlam i (cycles i)
  exact ⟨hexp, honeLoss,
    net_mobile_mass_le_unhit_true_holes_plus_global_soft_incidence
      B k hexp honeLoss⟩


#print axioms planar_net_mobile_true_hole_refund_shadow_ledger

end ProjectionOrdered
end JSP000404Research
