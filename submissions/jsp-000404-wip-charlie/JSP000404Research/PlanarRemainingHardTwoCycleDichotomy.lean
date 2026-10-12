import JSP000404Research.PlanarRemainingRigidTwoCycleTight
import Mathlib.Tactic

/-!
# Geometric two-centre endgame for the genuinely unpaid hard remainder

Once the full-face hard reservation and BOTH orientations of mixed-rigid
partial surplus payments are subtracted, every remaining hard word
belongs to one of two sharply different source mechanisms:

* an OUTGOING / inactive transportable hard carrier (whole-face safe
  flip into the upper cube, but the image is still covered); or
* a RIGID hard carrier whose BOTH genuine planar centres possess
  stepwise-tight top-band cyclic-gap and wrap-equality certificates.

The second branch is a concrete PAIR of geometric local cycle equality
patterns, not an arbitrary abstract saturating exponent pair.

No claim is made that these simultaneous tight centres are
geometrically impossible. No global Boolean-hole payment is inferred.
-/

namespace JSP000404Research
namespace ProjectionOrdered

open OrderedEdgeColoring
open DirectionData

/-- For a genuine planar AngleCap point configuration, every Boolean
hard word remaining after the two mixed-rigid partial credits has a
transportable hard owner or an owner with BOTH endpoint cycles tight. -/
theorem planar_remaining_hard_transport_or_two_tight_cycles
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
    (word : Fin n → Bool)
    (hremaining :
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
      word ∈ remainingUnpaidHardAfterMixedRigidWords B k) :
    letI : LinearOrder (ProjectionOrdered V) := projectionLinearOrder hp
    let htpos : 0 < t := by
      rw [ht]
      have hnr : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
      linarith
    let hwidth : t < (n : ℝ) + 1 := by rw [ht]; linarith
    let D := genericDirectionData_sendov hp hcap htpos hlam
    let B := standardResidualColoring D n (by exact_mod_cast hwidth)
    let k : ProjectionOrdered V → ℕ :=
      fun i => centreExponent (cycles i) t
    let L : ∀ i : ProjectionOrdered V, LocalDirectionCycle D i :=
      fun i => projectionCutLocalCycle hp hcap htpos hlam i (cycles i)
    ∃ q : ProjectionOrdered V × ProjectionOrdered V,
      q ∈ hardOverlapCarrierPairs B ∧
      word ∈ carrierOverlapWords B q ∧
      (HasOutgoingHardTransport B q.1 q.2 ∨
       (q ∈ rigidHardOverlapCarrierPairs B ∧
        (∃ a : ℝ, ∃ xs : List ℝ,
          (L q.1).values = a :: xs ∧
          Nat.floor (xs.getLastD a) = n ∧
          InteriorBandGapTight a xs ∧
          excess (Nat.floor (a + t - xs.getLastD a)) = Nat.floor a) ∧
        (∃ a : ℝ, ∃ xs : List ℝ,
          (L q.2).values = a :: xs ∧
          Nat.floor (xs.getLastD a) = n ∧
          InteriorBandGapTight a xs ∧
          excess (Nat.floor (a + t - xs.getLastD a)) = Nat.floor a))) := by
  classical
  letI : LinearOrder (ProjectionOrdered V) := projectionLinearOrder hp
  have htpos : 0 < t := by
    rw [ht]
    have hnr : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    linarith
  have hwidth : t < (n : ℝ) + 1 := by rw [ht]; linarith
  have hdelta1 : delta < 1 := by linarith
  let D : DirectionData (ProjectionOrdered V) t :=
    genericDirectionData_sendov hp hcap htpos hlam
  let B : OrderedEdgeColoring (ProjectionOrdered V) (n + 1) :=
    standardResidualColoring D n (by exact_mod_cast hwidth)
  let k : ProjectionOrdered V → ℕ :=
    fun i => centreExponent (cycles i) t
  let L : ∀ i : ProjectionOrdered V, LocalDirectionCycle D i :=
    fun i => projectionCutLocalCycle hp hcap htpos hlam i (cycles i)
  change ∃ q : ProjectionOrdered V × ProjectionOrdered V,
      q ∈ hardOverlapCarrierPairs B ∧
      word ∈ carrierOverlapWords B q ∧
      (HasOutgoingHardTransport B q.1 q.2 ∨
       (q ∈ rigidHardOverlapCarrierPairs B ∧
        (∃ a : ℝ, ∃ xs : List ℝ,
          (L q.1).values = a :: xs ∧
          Nat.floor (xs.getLastD a) = n ∧
          InteriorBandGapTight a xs ∧
          excess (Nat.floor (a + t - xs.getLastD a)) = Nat.floor a) ∧
        (∃ a : ℝ, ∃ xs : List ℝ,
          (L q.2).values = a :: xs ∧
          Nat.floor (xs.getLastD a) = n ∧
          InteriorBandGapTight a xs ∧
          excess (Nat.floor (a + t - xs.getLastD a)) = Nat.floor a)))
  have hrem' :
      word ∈ remainingUnpaidHardAfterMixedRigidWords B k := by
    exact hremaining
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
  obtain ⟨q,hpair,hw,hbranch⟩ :=
    remaining_hard_word_transport_or_doubly_saturated_rigid
      B k hexp honeLoss hrem'
  refine ⟨q,hpair,hw,?_⟩
  rcases hbranch with hflip | ⟨hrigid,_hlo,_hhi⟩
  · exact Or.inl hflip
  · right
    have htight :=
      planar_remaining_rigid_pair_two_stepwise_tight_cycles
        hp hcap hn hdelta0 hdeltaHalf ht hlam cycles
        q word ⟨hrem',hrigid,hw⟩
    exact ⟨hrigid,htight.1,htight.2⟩

#print axioms planar_remaining_hard_transport_or_two_tight_cycles

end ProjectionOrdered
end JSP000404Research
