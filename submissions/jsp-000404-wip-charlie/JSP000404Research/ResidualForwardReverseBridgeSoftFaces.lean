import JSP000404Research.ResidualForwardReverseCollisionOrder
import Mathlib.Tactic

/-!
# Identify the ONLY soft faces that can absorb opposite-direction transport collisions

For a forward hard transportable carrier (a,v) and a reverse
strict-descent rigid carrier (b,z), an image collision at w forces
b<v with residual edge (b,v). Moreover the UNIQUE soft overlap
carrier of w is EXACTLY this bridge (b,v).

Hence cross-direction image collisions can live only on the
soft-overlap faces whose lower endpoints come from reverse rigid
hard carriers and whose upper endpoints come from forward mobile
hard carriers.

This is a proper candidate subfamily of the entire soft overlap
pool; we do NOT assume it is small or empty. The theorem works
without planar geometry and without any new axiom/sorry.
-/

namespace JSP000404Research
namespace OrderedEdgeColoring

noncomputable def forwardReverseBridgeSoftCarriers
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ) : Finset (V × V) := by
  classical
  exact (softOverlapCarrierPairs C).filter fun r =>
    ∃ p ∈ transportableHardOverlapCarrierPairs C,
      ∃ q ∈ netStrictDescentRigidCarriers C exponent,
        r.1 = q.1 ∧ r.2 = p.2

noncomputable def forwardReverseBridgeSoftWords
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ) : Finset (Fin n → Bool) :=
  (forwardReverseBridgeSoftCarriers C exponent).biUnion
    (carrierOverlapWords C)

theorem forwardReverseBridgeSoftWords_subset_soft
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ) :
    forwardReverseBridgeSoftWords C exponent ⊆
      softOverlapCompletionWords C := by
  classical
  intro w hw
  obtain ⟨r,hr,hword⟩ := Finset.mem_biUnion.mp hw
  have hsoft :
      r ∈ softOverlapCarrierPairs C :=
    (Finset.mem_filter.mp hr).1
  change w ∈ (softOverlapCarrierPairs C).biUnion (carrierOverlapWords C)
  exact Finset.mem_biUnion.mpr ⟨r,hsoft,hword⟩

/-- The residual bridge forced by a collision IS its unique SOFT
word-owning residual carrier; no other soft carrier can own w. -/
theorem forward_reverse_sink_collision_has_bridge_soft_owner
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexp : ∀ x, exponent x ≤ n)
    (honeLoss : ∀ x, (active C x).card ≤ n - exponent x + 1)
    (x : {word : Fin n → Bool //
      word ∈ transportableHardOverlapCompletionWords C})
    (y : {word : Fin n → Bool //
      word ∈ netStrictDescentRigidWords C exponent})
    (hcollision :
      (transportableHardWordToSingletonOrSoft C x).1 =
      (strictDescentRigidWordToSingletonOrSoft
        C exponent hexp honeLoss y).1) :
    let p := transportableWordCarrier C x
    let q := strictDescentRigidWordCarrier C exponent y
    (q.1.1,p.1.2) ∈ softOverlapCarrierPairs C ∧
      (transportableHardWordToSingletonOrSoft C x).1 ∈
        carrierOverlapWords C (q.1.1,p.1.2) := by
  classical
  let p := transportableWordCarrier C x
  let q := strictDescentRigidWordCarrier C exponent y
  let w := (transportableHardWordToSingletonOrSoft C x).1
  have hb := forward_reverse_sink_collision_forces_backward_residual_bridge
    C exponent hexp honeLoss x y hcollision
  change q.1.1 < p.1.2 ∧ IsResidual C q.1.1 p.1.2 at hb
  have hwUpper : w ∈ retainedCompletionWords C p.1.2 :=
    transportableHardWordToSingletonOrSoft_mem_upper C x
  have hwLower : w ∈ retainedCompletionWords C q.1.1 := by
    change (transportableHardWordToSingletonOrSoft C x).1 ∈
      retainedCompletionWords C q.1.1
    rw [hcollision]
    exact strictDescentRigidWordToSingletonOrSoft_mem_lower
      C exponent hexp honeLoss y
  have hwBridge : w ∈ carrierOverlapWords C (q.1.1,p.1.2) :=
    Finset.mem_inter.mpr ⟨hwLower,hwUpper⟩
  have hsoft := forward_reverse_sink_collision_is_soft
    C exponent hexp honeLoss x y hcollision
  change w ∈ (softOverlapCarrierPairs C).biUnion (carrierOverlapWords C)
    at hsoft
  obtain ⟨r,hr,hwr⟩ := Finset.mem_biUnion.mp hsoft
  have hresR : r ∈ residualCarrierPairs C :=
    ((mem_overlapCarrierPairs C r).1
      ((mem_softOverlapCarrierPairs C r).1 hr).1).1
  have hrOrder := ((mem_residualCarrierPairs C r.1 r.2).1 hresR).1
  have heq := completion_word_unique_ordered_pair
    C hb.1 hrOrder hwLower hwUpper
      (Finset.mem_inter.mp hwr).1 (Finset.mem_inter.mp hwr).2
  have hbridgeEq : (q.1.1,p.1.2) = r :=
    Prod.ext heq.1 heq.2
  have hbridgeSoft : (q.1.1,p.1.2) ∈ softOverlapCarrierPairs C := by
    simpa only [hbridgeEq] using hr
  exact ⟨hbridgeSoft,hwBridge⟩

theorem forward_reverse_sink_collision_in_bridge_soft_words
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexp : ∀ x, exponent x ≤ n)
    (honeLoss : ∀ x, (active C x).card ≤ n - exponent x + 1)
    (x : {word : Fin n → Bool //
      word ∈ transportableHardOverlapCompletionWords C})
    (y : {word : Fin n → Bool //
      word ∈ netStrictDescentRigidWords C exponent})
    (hcollision :
      (transportableHardWordToSingletonOrSoft C x).1 =
      (strictDescentRigidWordToSingletonOrSoft
        C exponent hexp honeLoss y).1) :
    (transportableHardWordToSingletonOrSoft C x).1 ∈
      forwardReverseBridgeSoftWords C exponent := by
  classical
  let p := transportableWordCarrier C x
  let q := strictDescentRigidWordCarrier C exponent y
  have hp := (transportableWordCarrier C x).2
  have hq := (strictDescentRigidWordCarrier C exponent y).2
  have hb := forward_reverse_sink_collision_has_bridge_soft_owner
    C exponent hexp honeLoss x y hcollision
  change (q.1.1,p.1.2) ∈ softOverlapCarrierPairs C ∧
      (transportableHardWordToSingletonOrSoft C x).1 ∈
        carrierOverlapWords C (q.1.1,p.1.2) at hb
  have hcandidate :
      (q.1.1,p.1.2) ∈ forwardReverseBridgeSoftCarriers C exponent := by
    apply Finset.mem_filter.mpr
    exact ⟨hb.1,⟨p.1,hp,q.1,hq,rfl,rfl⟩⟩
  exact Finset.mem_biUnion.mpr ⟨(q.1.1,p.1.2),hcandidate,hb.2⟩

#print axioms forward_reverse_sink_collision_has_bridge_soft_owner
#print axioms forward_reverse_sink_collision_in_bridge_soft_words
#print axioms forwardReverseBridgeSoftWords_subset_soft

end OrderedEdgeColoring
end JSP000404Research
