import JSP000404Research.PlanarOverweightRealResidualCollision
import JSP000404Research.DirectionDataHallExactCycleTight
import JSP000404Research.ProjectionSaturatedBandEquality
import Mathlib.Tactic

/-!
# Hard carrier in a true planar overweight counterexample has a tight endpoint

This module bypasses the presently unverified downstream legacy
ProjectionSaturatedStepRigidity/EndpointDichotomy modules. It assembles
ONLY kernel-checked underlying inputs:

* genuine overweight -> a projected-loss centre OR a shared completion
  word on an actual residual edge with an exact-saturated endpoint;
* exact/non-loss + residual-active -> full-band stepwise cyclic-gap equality;
* a residual top-band edge forces the saturated endpoint's last local
  direction value to have integer floor n.

In the hard-carrier case the shared residual edge and the full rigid
local-cycle profile are bundled into one concrete planar witness.

The stronger zero-first-or-zero-quotient-unit-step endpoint dichotomy
is NOT asserted until its independent dependency chain is compiled.
This necessary obstruction is not a proof of the global dyadic bound.
-/

namespace JSP000404Research
namespace ProjectionOrdered

open OrderedEdgeColoring
open DirectionData

/-- Any overweight lower-branch planar configuration either has a projected
loss vertex or an actual shared-word residual edge with one stepwise-tight,
top-band-saturated endpoint. -/
theorem planar_overweight_loss_or_hard_carrier_stepwise_top_witness
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
        CentreProjectiveCycle (reindexedPoint_injective hp) i)
    (hover :
      letI : LinearOrder (ProjectionOrdered V) :=
        projectionLinearOrder hp
      2 ^ n < ∑ i : ProjectionOrdered V,
        2 ^ centreExponent (cycles i) t) :
    letI : LinearOrder (ProjectionOrdered V) :=
      projectionLinearOrder hp
    let hpos : 0 < t := by
      rw [ht]
      have hnR : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
      linarith
    let hwidth : t < (n : ℝ) + 1 := by rw [ht]; linarith
    let D := genericDirectionData_sendov hp hcap hpos hlam
    let B := standardResidualColoring D n (by exact_mod_cast hwidth)
    let k : ProjectionOrdered V → ℕ :=
      fun i => centreExponent (cycles i) t
    (∃ i : ProjectionOrdered V,
      i ∈ projectedLossVertices B k) ∨
      (∃ (u v : ProjectionOrdered V) (word : Fin n → Bool),
        u < v ∧
        IsResidual B u v ∧
        word ∈ retainedCompletionWords B u ∧
        word ∈ retainedCompletionWords B v ∧
        Nat.floor (D.value u v) = n ∧
        ∃ i : ProjectionOrdered V,
          (i = u ∨ i = v) ∧
          k i = projectedFree B i ∧
          ∃ a : ℝ, ∃ xs : List ℝ,
            (projectionCutLocalCycle hp hcap hpos hlam
              i (cycles i)).values = a :: xs ∧
            Nat.floor (xs.getLastD a) = n ∧
            InteriorBandGapTight a xs ∧
            excess (Nat.floor (a + t - xs.getLastD a)) =
              Nat.floor a) := by
  classical
  letI : LinearOrder (ProjectionOrdered V) := projectionLinearOrder hp
  have hpos : 0 < t := by
      rw [ht]
      have hnR : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
      linarith
  have hwidth : t < (n : ℝ) + 1 := by
    rw [ht]
    linarith
  let D : DirectionData (ProjectionOrdered V) t :=
    genericDirectionData_sendov hp hcap hpos hlam
  let B : OrderedEdgeColoring (ProjectionOrdered V) (n + 1) :=
    standardResidualColoring D n (by exact_mod_cast hwidth)
  let L : ∀ i : ProjectionOrdered V, LocalDirectionCycle D i :=
    fun i => projectionCutLocalCycle hp hcap hpos hlam i (cycles i)
  let k : ProjectionOrdered V → ℕ :=
    fun i => centreExponent (cycles i) t
  change
    (∃ i : ProjectionOrdered V, i ∈ projectedLossVertices B k) ∨
      (∃ (u v : ProjectionOrdered V) (word : Fin n → Bool),
        u < v ∧ IsResidual B u v ∧
        word ∈ retainedCompletionWords B u ∧
        word ∈ retainedCompletionWords B v ∧
        Nat.floor (D.value u v) = n ∧
        ∃ i : ProjectionOrdered V,
          (i = u ∨ i = v) ∧
          k i = projectedFree B i ∧
          ∃ a : ℝ, ∃ xs : List ℝ,
            (L i).values = a :: xs ∧
            Nat.floor (xs.getLastD a) = n ∧
            InteriorBandGapTight a xs ∧
            excess (Nat.floor (a + t - xs.getLastD a)) =
              Nat.floor a)
  have hbase :=
    planar_overweight_has_loss_or_real_saturated_residual_collision
      hp hcap hpos hlam hwidth cycles hover
  change
    (∃ i : ProjectionOrdered V, i ∈ projectedLossVertices B k) ∨
      (∃ (u v : ProjectionOrdered V) (word : Fin n → Bool),
        u < v ∧ IsResidual B u v ∧
        word ∈ retainedCompletionWords B u ∧
        word ∈ retainedCompletionWords B v ∧
        (k u = projectedFree B u ∨
          k v = projectedFree B v)) at hbase
  rcases hbase with hloss | hcarrier
  · exact Or.inl hloss
  · right
    obtain ⟨u, v, word, huv, hres, huWord, hvWord, hsat⟩ := hcarrier
    have hfloor : Nat.floor (D.value u v) = n := by
      have hx0 : 0 ≤ D.value u v := D.nonnegative huv
      have hxn : (n : ℝ) ≤ D.value u v :=
        (standardResidual_iff_high
          D n (by exact_mod_cast hwidth) huv).1 hres
      have htop : D.value u v < (n : ℝ) + 1 :=
        (D.belowWidth huv).trans hwidth
      exact (Nat.floor_eq_iff hx0).2 ⟨hxn, htop⟩
    have hactive :=
      residualCoord_mem_active_of_isResidual B huv hres
    have hExp : ∀ i : ProjectionOrdered V, (L i).exponent = k i := by
      intro i
      exact projectionCutLocalCycle_exponent_eq_centreExponent
        hp hcap hpos hlam i (cycles i)
    have hrigid (i : ProjectionOrdered V)
        (hki : k i = projectedFree B i)
        (hiActive : residualCoord n ∈ active B i) :
        ∃ a : ℝ, ∃ xs : List ℝ,
          (L i).values = a :: xs ∧
          Nat.floor (xs.getLastD a) = n ∧
          InteriorBandGapTight a xs ∧
          excess (Nat.floor (a + t - xs.getLastD a)) =
            Nat.floor a := by
      have hiExact : (L i).exponent = projectedFree B i := by
        rw [hExp i]
        exact hki
      obtain ⟨a, xs, hvals, hStep, hWrap⟩ :=
        exact_nonloss_residual_active_local_cycle_rigid
          D hwidth L i hiExact hiActive
      have htopBand : residualCoord n ∈ D.incidentBands (n + 1) i := by
        have heq :=
          standardResidual_active_eq_incidentBands_succ
            D n (by exact_mod_cast hwidth) i
        rw [← heq]
        exact hiActive
      have hlast : Nat.floor (xs.getLastD a) = n :=
        localDirection_last_floor_eq_top_of_topBand_mem
          D (L i) hwidth htopBand hvals
      have hwrap' :
          excess (Nat.floor (a + t - xs.getLastD a)) =
            Nat.floor a := by
        rw [hlast] at hWrap
        simpa using hWrap
      exact ⟨a, xs, hvals, hlast, hStep, hwrap'⟩
    refine ⟨u, v, word, huv, hres, huWord, hvWord, hfloor, ?_⟩
    rcases hsat with huSat | hvSat
    · exact ⟨u, Or.inl rfl, huSat, hrigid u huSat hactive.1⟩
    · exact ⟨v, Or.inr rfl, hvSat, hrigid v hvSat hactive.2⟩

#print axioms planar_overweight_loss_or_hard_carrier_stepwise_top_witness

end ProjectionOrdered
end JSP000404Research
