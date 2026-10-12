import JSP000404Research.ResidualTerminalDoubleSaturatedHard
import JSP000404Research.PlanarStandardResidualBudget
import JSP000404Research.PlanarOverweightHardCarrierPhaseWitness
import Mathlib.Tactic

/-!
# Two simultaneous genuine planar cycle-rigidity witnesses

After the globally verified whole-face and both mixed-rigid
partial reservations, a remaining rigid hard overlap is doubly
projected-saturated under the genuine planar one-layer budget.

Unlike the prior overweight witness that only exhibited ONE tight
endpoint, this theorem produces TWO independent full-cycle
stepwise-tight certificates for the SAME still-unpaid rigid face.
Both endpoints have top-band last-direction floor exactly n and
wrap-gap equality. The actual planar coordinates, centres and
source projection cuts are retained in the statement.

This is a NECESSARY CONDITION, not an impossibility theorem.
No new global Boolean-hole payment is claimed.
-/

namespace JSP000404Research
namespace ProjectionOrdered

open OrderedEdgeColoring
open DirectionData

/-- Every still-unpaid doubly-saturated RIGID hard face in a
genuine planar AngleCap configuration forces full-band
stepwise-tight local projective direction cycles at BOTH endpoints. -/
theorem planar_remaining_rigid_pair_two_stepwise_tight_cycles
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
        CentreProjectiveCycle (reindexedPoint_injective hp) i)
    (q : ProjectionOrdered V × ProjectionOrdered V)
    (word : Fin n → Bool)
    (hrem :
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
      word ∈ remainingUnpaidHardAfterMixedRigidWords B k ∧
        q ∈ rigidHardOverlapCarrierPairs B ∧
        word ∈ carrierOverlapWords B q) :
    letI : LinearOrder (ProjectionOrdered V) := projectionLinearOrder hp
    let htpos : 0 < t := by
      rw [ht]
      have hnr : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
      linarith
    let D := genericDirectionData_sendov hp hcap htpos hlam
    let L : ∀ i : ProjectionOrdered V, LocalDirectionCycle D i :=
      fun i => projectionCutLocalCycle hp hcap htpos hlam i (cycles i)
    (∃ a : ℝ, ∃ xs : List ℝ,
      (L q.1).values = a :: xs ∧
      Nat.floor (xs.getLastD a) = n ∧
      InteriorBandGapTight a xs ∧
      excess (Nat.floor (a + t - xs.getLastD a)) = Nat.floor a)
    ∧
    (∃ a : ℝ, ∃ xs : List ℝ,
      (L q.2).values = a :: xs ∧
      Nat.floor (xs.getLastD a) = n ∧
      InteriorBandGapTight a xs ∧
      excess (Nat.floor (a + t - xs.getLastD a)) = Nat.floor a) := by
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
  let D : DirectionData (ProjectionOrdered V) t :=
    genericDirectionData_sendov hp hcap htpos hlam
  let B : OrderedEdgeColoring (ProjectionOrdered V) (n + 1) :=
    standardResidualColoring D n (by exact_mod_cast hwidth)
  let k : ProjectionOrdered V → ℕ :=
    fun i => centreExponent (cycles i) t
  let L : ∀ i : ProjectionOrdered V, LocalDirectionCycle D i :=
    fun i => projectionCutLocalCycle hp hcap htpos hlam i (cycles i)
  change
    (∃ a : ℝ, ∃ xs : List ℝ,
      (L q.1).values = a :: xs ∧
      Nat.floor (xs.getLastD a) = n ∧
      InteriorBandGapTight a xs ∧
      excess (Nat.floor (a + t - xs.getLastD a)) = Nat.floor a) ∧
    (∃ a : ℝ, ∃ xs : List ℝ,
      (L q.2).values = a :: xs ∧
      Nat.floor (xs.getLastD a) = n ∧
      InteriorBandGapTight a xs ∧
      excess (Nat.floor (a + t - xs.getLastD a)) = Nat.floor a)
  have hrem' :
      word ∈ remainingUnpaidHardAfterMixedRigidWords B k ∧
        q ∈ rigidHardOverlapCarrierPairs B ∧
        word ∈ carrierOverlapWords B q := by
    exact hrem
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
  obtain ⟨hsatLo, hsatHi⟩ :=
    remaining_rigid_hard_word_both_endpoints_saturated
      B k hexp honeLoss hrem'.1 hrem'.2.1 hrem'.2.2
  have hhard : q ∈ hardOverlapCarrierPairs B :=
    ((mem_rigidHardOverlapCarrierPairs B q).1 hrem'.2.1).1
  have hresPair : q.1 < q.2 ∧ IsResidual B q.1 q.2 :=
    (mem_residualCarrierPairs B _ _).1
      ((mem_overlapCarrierPairs B q).1
        ((mem_hardOverlapCarrierPairs B q).1 hhard).1).1
  have hactive :=
    residualCoord_mem_active_of_isResidual B hresPair.1 hresPair.2
  have hExp : ∀ i : ProjectionOrdered V,
      (L i).exponent = k i := by
    intro i
    exact projectionCutLocalCycle_exponent_eq_centreExponent
      hp hcap htpos hlam i (cycles i)
  have hcycleTight (i : ProjectionOrdered V)
      (hiSat : k i = projectedFree B i)
      (hiActive : residualCoord n ∈ active B i) :
      ∃ a : ℝ, ∃ xs : List ℝ,
        (L i).values = a :: xs ∧
        Nat.floor (xs.getLastD a) = n ∧
        InteriorBandGapTight a xs ∧
        excess (Nat.floor (a + t - xs.getLastD a)) = Nat.floor a := by
    have hiExact : (L i).exponent = projectedFree B i := by
      rw [hExp i]
      exact hiSat
    obtain ⟨a, xs, hvals, hStep, hWrap⟩ :=
      exact_nonloss_residual_active_local_cycle_rigid
        D hwidth L i hiExact hiActive
    have htopBand :
        residualCoord n ∈ D.incidentBands (n + 1) i := by
      have hbands :=
        standardResidual_active_eq_incidentBands_succ
          D n (by exact_mod_cast hwidth) i
      rw [← hbands]
      exact hiActive
    have hlast : Nat.floor (xs.getLastD a) = n :=
      localDirection_last_floor_eq_top_of_topBand_mem
        D (L i) hwidth htopBand hvals
    have hwrap' :
        excess (Nat.floor (a + t - xs.getLastD a)) = Nat.floor a := by
      rw [hlast] at hWrap
      simpa using hWrap
    exact ⟨a, xs, hvals, hlast, hStep, hwrap'⟩
  exact ⟨hcycleTight q.1 hsatLo hactive.1,
    hcycleTight q.2 hsatHi hactive.2⟩

#print axioms planar_remaining_rigid_pair_two_stepwise_tight_cycles

end ProjectionOrdered
end JSP000404Research
