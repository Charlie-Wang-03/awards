import JSP000404Research.InteriorPhaseSlipExactProjectedLoss
import JSP000404Research.ResidualCompletionMultiplicity
import Mathlib.Tactic

/-!
# Exact characterization of a projected-loss centre for any direction width

For ANY DirectionData with t < n+1 and any local direction cycles,
  projected loss at i
    <=> local (n+1)-band capacity is tight at i AND residual colour
        is inactive at i.

The reverse direction uses the full-band local inequality, the
retained-active subset of the full active palette, and the identity
between full-band incident colours and the active palette.

As a consequence, every projected-loss centre admits actual
consecutive neighbouring rays with an integer-band unit crossing
shorter than one normalized unit, and two adjacent retained active
Boolean coordinates. No half-unit upper bound on fractional t is
needed for this implication.

This does NOT solve global collision-free payment of the loss cubes.
-/

namespace JSP000404Research
namespace DirectionData

open OrderedEdgeColoring

/-- A projected-loss vertex necessarily saturates the (n+1)-band
local budget and does not use the residual colour. -/
theorem projected_loss_forces_tight_and_residual_inactive
    {V : Type*} [LinearOrder V] [Fintype V]
    {t : ℝ} {n : ℕ}
    (D : DirectionData V t)
    (ht : t < (n : ℝ) + 1)
    (cycles : ∀ i : V, LocalDirectionCycle D i)
    (i : V)
    (hloss :
      i ∈ projectedLossVertices
        (standardResidualColoring D n
          (by exact_mod_cast ht))
        (fun j => (cycles j).exponent)) :
    (cycles i).exponent +
        (D.incidentBands (n + 1) i).card = n + 1 ∧
      residualCoord n ∉ active
        (standardResidualColoring D n
          (by exact_mod_cast ht)) i := by
  classical
  let B : OrderedEdgeColoring V (n + 1) :=
    standardResidualColoring D n (by exact_mod_cast ht)
  have heq :
      (cycles i).exponent = projectedFree B i + 1 :=
    (mem_projectedLossVertices B
      (fun j => (cycles j).exponent) i).1 hloss
  have hret :
      (retainedActive B i).card ≤ n := by
    simpa using Finset.card_le_univ (retainedActive B i)
  have hsubset := retainedActive_card_le_active B i
  have hactive :
      active B i = D.incidentBands (n + 1) i :=
    standardResidual_active_eq_incidentBands_succ
      D n (by exact_mod_cast ht) i
  have hlocal :
      (cycles i).exponent + (active B i).card ≤ n + 1 := by
    rw [hactive]
    exact (cycles i).exponent_add_incidentBands_card_le ht
  have hbudget :
      (cycles i).exponent +
        (active B i).card = n + 1 := by
    dsimp [projectedFree] at heq
    omega
  constructor
  · rw [← hactive]
    exact hbudget
  · intro hres
    have hdrop :=
      retainedActive_card_add_one_le_active_of_residual_mem
        B i hres
    dsimp [projectedFree] at heq
    omega

/-- Full necessary-and-sufficient structural classification of
exact projected loss, independent of lower-branch delta thresholds. -/
theorem projected_loss_iff_tight_and_residual_inactive
    {V : Type*} [LinearOrder V] [Fintype V]
    {t : ℝ} {n : ℕ}
    (D : DirectionData V t)
    (ht : t < (n : ℝ) + 1)
    (cycles : ∀ i : V, LocalDirectionCycle D i)
    (i : V) :
    i ∈ projectedLossVertices
        (standardResidualColoring D n
          (by exact_mod_cast ht))
        (fun j => (cycles j).exponent) ↔
      ((cycles i).exponent +
          (D.incidentBands (n + 1) i).card = n + 1 ∧
        residualCoord n ∉ active
          (standardResidualColoring D n
            (by exact_mod_cast ht)) i) := by
  constructor
  · exact projected_loss_forces_tight_and_residual_inactive
      D ht cycles i
  · rintro ⟨htight,hinactive⟩
    exact LocalDirectionCycle.mem_projectedLoss_of_local_tight_residual_inactive
      D ht cycles i htight hinactive

/-- Every projected loss in an arbitrary direction cycle has two
adjacent retained active Boolean band coordinates. -/
theorem projected_loss_has_adjacent_retained_bands
    {V : Type*} [LinearOrder V] [Fintype V]
    {t : ℝ} {n : ℕ}
    (D : DirectionData V t)
    (ht : t < (n : ℝ) + 1)
    (cycles : ∀ i : V, LocalDirectionCycle D i)
    (i : V)
    (hloss :
      i ∈ projectedLossVertices
        (standardResidualColoring D n
          (by exact_mod_cast ht))
        (fun j => (cycles j).exponent)) :
    ∃ c d : Fin n,
      c.val + 1 = d.val ∧
      c ∈ retainedActive (standardResidualColoring D n
        (by exact_mod_cast ht)) i ∧
      d ∈ retainedActive (standardResidualColoring D n
        (by exact_mod_cast ht)) i := by
  obtain ⟨htight,hinactive⟩ :=
    projected_loss_forces_tight_and_residual_inactive
      D ht cycles i hloss
  exact (cycles i).exists_adjacent_retained_active_bands_of_tight_inactive
    ht htight hinactive

/-- The existential geometric witness at every projected-loss vertex:
two actual consecutive rays cross an integer boundary but have
normalized angular gap strictly less than one. -/
theorem projected_loss_has_consecutive_short_band_crossing_rays
    {V : Type*} [LinearOrder V] [Fintype V]
    {t : ℝ} {n : ℕ}
    (D : DirectionData V t)
    (ht : t < (n : ℝ) + 1)
    (cycles : ∀ i : V, LocalDirectionCycle D i)
    (i : V)
    (hloss :
      i ∈ projectedLossVertices
        (standardResidualColoring D n
          (by exact_mod_cast ht))
        (fun j => (cycles j).exponent)) :
    ∃ (u v : OtherVertex i) (pre post : List (OtherVertex i)),
      (cycles i).rays = pre ++ u :: v :: post ∧
      0 ≤ D.localDirectionValue i v - D.localDirectionValue i u ∧
      D.localDirectionValue i v - D.localDirectionValue i u < 1 ∧
      Nat.floor (D.localDirectionValue i v) -
        Nat.floor (D.localDirectionValue i u) = 1 := by
  obtain ⟨htight,hinactive⟩ :=
    projected_loss_forces_tight_and_residual_inactive
      D ht cycles i hloss
  exact (cycles i).exists_adjacent_rays_with_short_band_crossing
    ht htight hinactive

#print axioms projected_loss_forces_tight_and_residual_inactive
#print axioms projected_loss_iff_tight_and_residual_inactive
#print axioms projected_loss_has_adjacent_retained_bands
#print axioms projected_loss_has_consecutive_short_band_crossing_rays

end DirectionData
end JSP000404Research
