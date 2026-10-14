import JSP000404Research.PlanarNetNineCentreTwinTradeoff
import JSP000404Research.ResidualNetCollisionTwinFibreDyadicTradeoff
import Mathlib.Tactic

/-!
# True planar AngleCap TWIN dyadic liability versus ACTUAL NET target fibres

For every real canonical target d, after deriving genuine exponent bounds
and one-layer active budget, the true planar structure certifies:

  TWIN dyadic mass <= (floor(|V|/2)-2*|F_d|) * 2^(n-1).

No original-centre size restriction. This is NOT a non-reusing true-hole
or globally unreserved profile-surplus payment.
-/

namespace JSP000404Research
namespace ProjectionOrdered

open OrderedEdgeColoring
open DirectionData

theorem planar_net_each_target_twin_fibre_dyadic_budget
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
        ∀ d : Fin n → Bool,
          (∑ q ∈ netTwinRigidCarriers B k, (2 : ℕ) ^ k q.2) ≤
          (Fintype.card V / 2 -
            2 * (netCollisionCertifiedDiagonalFibre B k hexp honeLoss d).card)
            * (2 : ℕ) ^ (n - 1) := by
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
        ∀ d : Fin n → Bool,
          (∑ q ∈ netTwinRigidCarriers B k, (2 : ℕ) ^ k q.2) ≤
          (Fintype.card V / 2 -
            2 * (netCollisionCertifiedDiagonalFibre B k hexp honeLoss d).card)
            * (2 : ℕ) ^ (n - 1)
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
  have hcardeq : Fintype.card (ProjectionOrdered V) = Fintype.card V := by
    let e : ProjectionOrdered V ≃ V :=
      { toFun := ProjectionOrdered.toOriginal
        invFun := ProjectionOrdered.ofOriginal
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
    exact Fintype.card_congr e
  refine ⟨hexp, honeLoss, ?_⟩
  intro d
  have h := net_collision_twin_mass_le_fibre_adjusted_dyadic_budget
    B k hexp honeLoss hstrict d
  rw [hcardeq] at h
  exact h

#print axioms planar_net_each_target_twin_fibre_dyadic_budget

end ProjectionOrdered
end JSP000404Research
