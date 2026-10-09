import JSP000404Research.PlanarGlobalOverweightRigidity
import Mathlib.Tactic

/-!
# The complete n+1 band budget must be tight in any overweight configuration

The global completion-mass proof gives a dichotomy:
 * projected-loss vertex, whose full-band cyclic budget is exact;
 * residual-active exact projected saturation, whose full-band budget is exact.

This proves a simple geometric obstruction that is NOT a disguised
minimal-Hall assumption: the original full (n+1)-colour local cyclic
budget must saturate at some centre whenever the n-bit bound fails.

The planar specialization uses the actual canonical cut/rotated projective
cycle and preserves its exponent. Therefore configurations with at least
one full-band unit of slack at every centre already obey the target bound.

A tight centre alone does not force the target inequality or a
contradiction; the remaining global geometric accounting stays open.
-/

namespace JSP000404Research
namespace DirectionData

open OrderedEdgeColoring

theorem overweight_directionData_has_full_band_tight_centre
    {V : Type*} [LinearOrder V] [Fintype V]
    {t : ℝ} {n : ℕ}
    (D : DirectionData V t)
    (ht : t < (n : ℝ) + 1)
    (cycles : ∀ i : V, LocalDirectionCycle D i)
    (hover : 2 ^ n < ∑ i : V, 2 ^ (cycles i).exponent) :
    ∃ i : V,
      (cycles i).exponent + (D.incidentBands (n + 1) i).card =
        n + 1 := by
  classical
  let B : OrderedEdgeColoring V (n + 1) :=
    standardResidualColoring D n (by exact_mod_cast ht)
  let k : V → ℕ := fun i => (cycles i).exponent
  have hprof := localCycles_standardResidual_oneLayer_profile D ht cycles
  have hexp : ∀ v, k v ≤ n := hprof.1
  have honeActive :
      ∀ v, (active B v).card ≤ n - k v + 1 := hprof.2
  have hone :
      ∀ v, k v ≤ projectedFree B v + 1 :=
    exponent_le_projectedFree_add_one B k hexp honeActive
  have hresBudget :
      ∀ v, residualCoord n ∈ active B v →
        k v ≤ projectedFree B v := by
    intro v hvRes
    have hdrop :=
      retainedActive_card_add_one_le_active_of_residual_mem B v hvRes
    have hvBound := honeActive v
    have hvExp : k v ≤ n := hexp v
    have hvCard :
        (retainedActive B v).card ≤ n := by
      simpa using Finset.card_le_univ (retainedActive B v)
    dsimp [projectedFree]
    omega
  have hob : 2 ^ n < ∑ i : V, 2 ^ k i := hover
  rcases overweight_forces_loss_or_residual_saturation
      B k hone hresBudget hob with hloss | hsat
  · obtain ⟨i, hiLoss⟩ := hloss
    exact ⟨i,
      (projected_loss_forces_tight_and_residual_inactive
        D ht cycles i hiLoss).1⟩
  · obtain ⟨i, hiRes, hiSat⟩ := hsat
    exact ⟨i,
      exact_nonloss_residual_active_full_band_tight
        D ht cycles i hiSat hiRes⟩

/-- Contrapositive: genuinely strict local full-band budgets at
all centres imply the n-bit global dyadic capacity. -/
theorem directionData_dyadic_capacity_of_all_full_band_strict
    {V : Type*} [LinearOrder V] [Fintype V]
    {t : ℝ} {n : ℕ}
    (D : DirectionData V t)
    (ht : t < (n : ℝ) + 1)
    (cycles : ∀ i : V, LocalDirectionCycle D i)
    (hstrict : ∀ i : V,
      (cycles i).exponent + (D.incidentBands (n + 1) i).card < n + 1) :
    (∑ i : V, 2 ^ (cycles i).exponent) ≤ 2 ^ n := by
  by_contra h
  have hover : 2 ^ n < ∑ i : V, 2 ^ (cycles i).exponent := by
    omega
  obtain ⟨i, htight⟩ :=
    overweight_directionData_has_full_band_tight_centre
      D ht cycles hover
  have hi := hstrict i
  omega

#print axioms overweight_directionData_has_full_band_tight_centre
#print axioms directionData_dyadic_capacity_of_all_full_band_strict

end DirectionData

namespace ProjectionOrdered

open DirectionData

/-- Actual planar point configurations with strict full-band capacity at
EVERY cut/rotated centre satisfy the sharp n-bit lower-branch bound.
No Hall-G1 exclusion is invoked. -/
theorem planar_dyadic_capacity_of_all_canonical_full_band_strict
    {V : Type*} [Fintype V]
    {p : V → Plane}
    (hp : Function.Injective p)
    {lam t : ℝ} {n : ℕ}
    (hcap : AngleCap p lam)
    (htpos : 0 < t)
    (hlam : lam = Real.pi / t)
    (hwidth : t < (n : ℝ) + 1)
    (cycles :
      letI : LinearOrder (ProjectionOrdered V) :=
        projectionLinearOrder hp
      ∀ i : ProjectionOrdered V,
        CentreProjectiveCycle (reindexedPoint_injective hp) i)
    (hstrict :
      letI : LinearOrder (ProjectionOrdered V) :=
        projectionLinearOrder hp
      let D := genericDirectionData_sendov hp hcap htpos hlam
      let C : ∀ i : ProjectionOrdered V, LocalDirectionCycle D i :=
        fun i => projectionCutLocalCycle hp hcap htpos hlam i (cycles i)
      ∀ i : ProjectionOrdered V,
        (C i).exponent + (D.incidentBands (n + 1) i).card < n + 1) :
    letI : LinearOrder (ProjectionOrdered V) :=
      projectionLinearOrder hp
    (∑ i : ProjectionOrdered V, 2 ^ centreExponent (cycles i) t) ≤
      2 ^ n := by
  classical
  letI : LinearOrder (ProjectionOrdered V) := projectionLinearOrder hp
  let D : DirectionData (ProjectionOrdered V) t :=
    genericDirectionData_sendov hp hcap htpos hlam
  let C : ∀ i : ProjectionOrdered V, LocalDirectionCycle D i :=
    fun i => projectionCutLocalCycle hp hcap htpos hlam i (cycles i)
  have hcapLocal :
      (∑ i : ProjectionOrdered V, 2 ^ (C i).exponent) ≤ 2 ^ n :=
    directionData_dyadic_capacity_of_all_full_band_strict
      D hwidth C hstrict
  have hExp : ∀ i : ProjectionOrdered V,
      (C i).exponent = centreExponent (cycles i) t := by
    intro i
    exact projectionCutLocalCycle_exponent_eq_centreExponent
      hp hcap htpos hlam i (cycles i)
  calc
    (∑ i : ProjectionOrdered V,
        2 ^ centreExponent (cycles i) t) =
      ∑ i : ProjectionOrdered V, 2 ^ (C i).exponent := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [hExp i]
    _ ≤ 2 ^ n := hcapLocal

#print axioms planar_dyadic_capacity_of_all_canonical_full_band_strict

end ProjectionOrdered
end JSP000404Research
