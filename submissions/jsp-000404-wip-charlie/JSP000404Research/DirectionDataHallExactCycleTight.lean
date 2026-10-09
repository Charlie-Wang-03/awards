import JSP000404Research.DirectionDataHallResidualActiveBoundary
import JSP000404Research.LinearBandGapStepTight
import Mathlib.Tactic

/-!
# Exact non-loss core witnesses force tight full-band cyclic gaps

For true DirectionData, an exact non-loss centre with an incident
residual edge exhausts the entire one-layer local band budget.
The equality case of the previously proved linear cyclic gap inequality
then makes every adjacent interior gap step tight (and forces the
wrap-gap equality).

In a loss-free inclusion-minimal Hall-deficient core, the existing
exact-nonloss residual-active witness supplies exactly such a centre.
No extra geometric hypothesis or sorry is introduced.
This is a necessary geometric rigidity of a hypothetical G1 core,
not an exclusion of that core.
-/

namespace JSP000404Research
namespace DirectionData

open OrderedEdgeColoring

/-- Exact projected-free exponent plus an active residual colour saturates
the ORIGINAL (n+1)-band local cyclic inequality. -/
theorem exact_nonloss_residual_active_full_band_tight
    {V : Type*} [LinearOrder V] [Fintype V]
    {t : ℝ} {n : ℕ}
    (D : DirectionData V t)
    (ht : t < (n : ℝ) + 1)
    (cycles : ∀ i : V, LocalDirectionCycle D i)
    (v : V)
    (hExact :
      (cycles v).exponent =
        projectedFree (standardResidualColoring D n (by exact_mod_cast ht)) v)
    (hResidual :
      residualCoord n ∈
        active (standardResidualColoring D n (by exact_mod_cast ht)) v) :
    (cycles v).exponent + (D.incidentBands (n + 1) v).card =
      n + 1 := by
  classical
  let B : OrderedEdgeColoring V (n + 1) :=
    standardResidualColoring D n (by exact_mod_cast ht)
  have hretN :
      (retainedActive B v).card ≤ n := by
    simpa using Finset.card_le_univ (retainedActive B v)
  have hEq :
      (cycles v).exponent + (retainedActive B v).card = n := by
    have he : (cycles v).exponent = n - (retainedActive B v).card := by
      simpa only [projectedFree] using hExact
    omega
  have hActiveLower :=
    retainedActive_card_add_one_le_active_of_residual_mem B v hResidual
  have hBudget := (cycles v).exponent_add_incidentBands_card_le ht
  have hPalette :
      active B v = D.incidentBands (n + 1) v :=
    standardResidual_active_eq_incidentBands_succ
      D n (by exact_mod_cast ht) v
  rw [← hPalette] at hBudget
  rw [← hPalette]
  omega

/-- Exact/non-loss residual-active centres also have a stepwise-tight
sorted local cyclic direction list and the equality-case wrap gap. -/
theorem exact_nonloss_residual_active_local_cycle_rigid
    {V : Type*} [LinearOrder V] [Fintype V]
    {t : ℝ} {n : ℕ}
    (D : DirectionData V t)
    (ht : t < (n : ℝ) + 1)
    (cycles : ∀ i : V, LocalDirectionCycle D i)
    (v : V)
    (hExact :
      (cycles v).exponent =
        projectedFree (standardResidualColoring D n (by exact_mod_cast ht)) v)
    (hResidual :
      residualCoord n ∈
        active (standardResidualColoring D n (by exact_mod_cast ht)) v) :
    ∃ a : ℝ, ∃ xs : List ℝ,
      (cycles v).values = a :: xs ∧
      InteriorBandGapTight a xs ∧
      excess (Nat.floor (a + t - xs.getLastD a)) =
        n - Nat.floor (xs.getLastD a) + Nat.floor a := by
  classical
  have htight :=
    exact_nonloss_residual_active_full_band_tight
      D ht cycles v hExact hResidual
  obtain ⟨a, xs, hvalues⟩ :
      ∃ a xs, (cycles v).values = a :: xs := by
    cases h : (cycles v).values with
    | nil =>
        exact False.elim ((cycles v).values_nonempty h)
    | cons a xs =>
        exact ⟨a, xs, rfl⟩
  have haMem : a ∈ (cycles v).values := by
    rw [hvalues]
    simp
  have ha0 : 0 ≤ a := ((cycles v).value_mem_bounds haMem).1
  have hsorted : (a :: xs).Pairwise (· ≤ ·) := by
    simpa only [hvalues] using (cycles v).values_pairwise
  have hall : ∀ x ∈ a :: xs, x < t := by
    intro x hx
    exact ((cycles v).value_mem_bounds
      (by simpa only [hvalues] using hx)).2
  have hwidth : t ≤ ((n + 1 : ℕ) : ℝ) := by
    push_cast
    linarith
  have hcard :=
    (cycles v).occupiedNatBands_values_card_eq_incidentBands_card
      (n + 1) hwidth
  rw [hvalues] at hcard
  have hEq :
      listExponent (linearCyclicGapQuotients t (a :: xs)) +
          (occupiedNatBands (a :: xs)).card =
        n + 1 := by
    have hb := htight
    unfold LocalDirectionCycle.exponent LocalDirectionCycle.gapQuotients at hb
    rw [hvalues] at hb
    rw [← hcard] at hb
    exact hb
  have hStep :=
    linear_cyclic_gapEquality_implies_stepwise_tight
      a xs ha0 hsorted hall ht hEq
  have hWrap :=
    wrap_gap_excess_eq_outer_empty_of_global_equality
      a xs ha0 hsorted hall ht hEq
  exact ⟨a, xs, hvalues, hStep, hWrap⟩

/-- A hypothetical loss-free minimal Hall obstruction in real direction
data has a centre with a genuinely tight stepwise cyclic gap profile. -/
theorem minimal_loss_free_deficient_core_has_tight_local_cycle
    {V : Type*} [LinearOrder V] [Fintype V]
    {t : ℝ} {n : ℕ}
    (D : DirectionData V t)
    (ht : t < (n : ℝ) + 1)
    (cycles : ∀ i : V, LocalDirectionCycle D i)
    {T : Finset V}
    (hdef :
      let B := standardResidualColoring D n (by exact_mod_cast ht)
      let k : V → ℕ := fun i => (cycles i).exponent
      BlockDeficient (fun i => 2 ^ k i)
        (enlargedProjectedCandidateBlock B k) T)
    (hmin :
      let B := standardResidualColoring D n (by exact_mod_cast ht)
      let k : V → ℕ := fun i => (cycles i).exponent
      ∀ U : Finset V, U ⊂ T →
        ¬ BlockDeficient (fun i => 2 ^ k i)
          (enlargedProjectedCandidateBlock B k) U)
    (hnoLoss :
      let B := standardResidualColoring D n (by exact_mod_cast ht)
      let k : V → ℕ := fun i => (cycles i).exponent
      ∀ v ∈ T, v ∉ projectedLossVertices B k) :
    ∃ v ∈ T,
      (cycles v).exponent =
        projectedFree
          (standardResidualColoring D n (by exact_mod_cast ht)) v ∧
      (∃ a : ℝ, ∃ xs : List ℝ,
        (cycles v).values = a :: xs ∧
        InteriorBandGapTight a xs ∧
        excess (Nat.floor (a + t - xs.getLastD a)) =
          n - Nat.floor (xs.getLastD a) + Nat.floor a) := by
  obtain ⟨v, hvT, hvExact, hvRes⟩ :=
    minimal_loss_free_deficient_core_has_residual_active_exact_nonloss
      D ht cycles hdef hmin hnoLoss
  exact ⟨v, hvT, hvExact,
    exact_nonloss_residual_active_local_cycle_rigid
      D ht cycles v hvExact hvRes⟩

#print axioms exact_nonloss_residual_active_full_band_tight
#print axioms exact_nonloss_residual_active_local_cycle_rigid
#print axioms minimal_loss_free_deficient_core_has_tight_local_cycle

end DirectionData
end JSP000404Research
