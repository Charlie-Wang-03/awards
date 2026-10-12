import JSP000404Research.ResidualNetActualCollisionStrictShellFibre
import Mathlib.Tactic

/-!
# Actual opposite hard transport collisions force TWO bit disagreements

For a true forward transport on hard carrier p=(a,v) and a
reverse strict-rigid transport on hard carrier q=(b,z), an actual
intersection of their target words w forces the soft bridge (b,v).

Beyond the already proved cross-active palette witnesses, EACH
of the two CHOSEN flip coordinates must have OPPOSITE retained
Boolean bits at the bridge endpoints b and v.

The first flip is at a colour active at a and b. Since hard p
has SameRetained a v, the bit disagreement across (a,b) also
occurs across (v,b). The reverse flip analogously proves the
other disagreement across (b,v) via SameRetained b z.

The flip coordinates are already proved distinct. Thus an ACTUAL
collision bridge has Hamming disagreement of at least TWO retained
bit coordinates, a stricter combinatorial filter than palette
incomparability alone. No new geometric postulate or true-hole
payment is introduced.
-/

namespace JSP000404Research
namespace OrderedEdgeColoring

noncomputable def retainedBitDisagreementCoords
    {V : Type*} [LinearOrder V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (u v : V) : Finset (Fin n) := by
  classical
  exact Finset.univ.filter
    (fun c => retainedBit C u c ≠ retainedBit C v c)

/-- When a SOURCE coordinate is active at a and a FLIPPED target
coordinate is active at b, the retained bits at a and b must
disagree at that coordinate. -/
theorem source_flip_target_active_bits_disagree
    {V : Type*} [LinearOrder V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    {a b : V} {c : Fin n} {word : Fin n → Bool}
    (ha : c ∈ retainedActive C a)
    (hb : c ∈ retainedActive C b)
    (hx : word ∈ retainedCompletionWords C a)
    (hw : flipCompletionWord c word ∈
      retainedCompletionWords C b) :
    retainedBit C a c ≠ retainedBit C b c := by
  have hbefore :=
    (mem_retainedCompletionWords C a word).1 hx c ha
  have hafter :=
    (mem_retainedCompletionWords C b
      (flipCompletionWord c word)).1 hw c hb
  rw [flipCompletionWord_at] at hafter
  intro heq
  have hfalse : (!word c) = word c :=
    hafter.trans (heq.symm.trans hbefore.symm)
  cases word c <;> simp at hfalse

/-- The two CHOSEN genuine transport colours witness opposite
retained-bit values at the two endpoints of their forced SOFT
bridge. This involves actual transported hard source words,
not an arbitrary pair of disjoint candidate colours. -/
theorem forward_reverse_actual_collision_two_bridge_bit_disagreements
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexp : ∀ v, exponent v ≤ n)
    (honeLoss : ∀ v, (active C v).card ≤ n - exponent v + 1)
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
    retainedBit C q.1.1 (transportablePairColor C p) ≠
      retainedBit C p.1.2 (transportablePairColor C p) ∧
    retainedBit C q.1.1
        (strictDescentRigidPairColor C exponent hexp honeLoss q) ≠
      retainedBit C p.1.2
        (strictDescentRigidPairColor C exponent hexp honeLoss q) := by
  classical
  let p := transportableWordCarrier C x
  let q := strictDescentRigidWordCarrier C exponent y
  let cf := transportablePairColor C p
  let cr := strictDescentRigidPairColor C exponent hexp honeLoss q
  have hcross :=
    forward_reverse_collision_cross_active_flip_colors
      C exponent hexp honeLoss x y hcollision
  change cf ∈ retainedActive C q.1.1 ∧
    cr ∈ retainedActive C p.1.2 at hcross
  have hpActive : cf ∈ retainedActive C p.1.1 := by
    rw [retainedActive_eq_incoming_union_outgoing C p.1.1]
    exact Finset.mem_union_right _
      (transportablePairColor_spec C p).1
  have hqActive : cr ∈ retainedActive C q.1.2 := by
    rw [retainedActive_eq_incoming_union_outgoing C q.1.2]
    exact Finset.mem_union_right _
      (strictDescentRigidPairColor_spec
        C exponent hexp honeLoss q).1
  have hxp := (Finset.mem_inter.mp
    (transportableWordCarrier_covers C x)).1
  have hyq := (Finset.mem_inter.mp
    (strictDescentRigidWordCarrier_covers C exponent y)).2
  have hwq :
      flipCompletionWord cf x.1 ∈
        retainedCompletionWords C q.1.1 := by
    have hw :
        (transportableHardWordToSingletonOrSoft C x).1 ∈
          retainedCompletionWords C q.1.1 := by
      rw [hcollision]
      exact strictDescentRigidWordToSingletonOrSoft_mem_lower
        C exponent hexp honeLoss y
    exact hw
  have hwp :
      flipCompletionWord cr y.1 ∈
        retainedCompletionWords C p.1.2 := by
    have hw :
        (strictDescentRigidWordToSingletonOrSoft
          C exponent hexp honeLoss y).1 ∈
          retainedCompletionWords C p.1.2 := by
      rw [← hcollision]
      exact transportableHardWordToSingletonOrSoft_mem_upper C x
    exact hw
  have hfbits : retainedBit C p.1.1 cf ≠
      retainedBit C q.1.1 cf :=
    source_flip_target_active_bits_disagree
      C hpActive hcross.1 hxp hwq
  have hrbits : retainedBit C q.1.2 cr ≠
      retainedBit C p.1.2 cr :=
    source_flip_target_active_bits_disagree
      C hqActive hcross.2 hyq hwp
  have hpInfo := (mem_transportableHardOverlapCarrierPairs
    C p.1).1 p.2
  have hpSame :=
    ((mem_hardOverlapCarrierPairs C p.1).1 hpInfo.1).2
  have hqInfo :=
    (mem_netStrictDescentRigidCarriers C exponent q.1).1 q.2
  have hqRigid :=
    (mem_netRigidHardCarriers C exponent q.1).1 hqInfo.1
  have hqHard :=
    ((mem_netUnpaidHardCarrierPairs C exponent q.1).1
      hqRigid.1).1
  have hqSame :=
    ((mem_hardOverlapCarrierPairs C q.1).1 hqHard).2
  constructor
  · intro heq
    exact hfbits ((hpSame cf).trans heq.symm)
  · intro heq
    exact hrbits ((hqSame cr).symm.trans heq)

/-- A genuinely colliding reverse-lower/forward-upper bridge has
retained-bit HAMMING DISAGREEMENT at least TWO. Its two witnessed
coordinates are exactly the distinct chosen hard transport flips. -/
theorem forward_reverse_actual_collision_bridge_hamming_ge_two
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexp : ∀ v, exponent v ≤ n)
    (honeLoss : ∀ v, (active C v).card ≤ n - exponent v + 1)
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
    2 ≤ (retainedBitDisagreementCoords C q.1.1 p.1.2).card := by
  classical
  let p := transportableWordCarrier C x
  let q := strictDescentRigidWordCarrier C exponent y
  let cf := transportablePairColor C p
  let cr := strictDescentRigidPairColor C exponent hexp honeLoss q
  have hbits :=
    forward_reverse_actual_collision_two_bridge_bit_disagreements
      C exponent hexp honeLoss x y hcollision
  change retainedBit C q.1.1 cf ≠ retainedBit C p.1.2 cf ∧
    retainedBit C q.1.1 cr ≠ retainedBit C p.1.2 cr at hbits
  have hne :=
    forward_reverse_actual_collision_distinct_flip_colors
      C exponent hexp honeLoss x y hcollision
  have hsub :
      ({cf,cr} : Finset (Fin n)) ⊆
        retainedBitDisagreementCoords C q.1.1 p.1.2 := by
    intro c hc
    simp only [Finset.mem_insert, Finset.mem_singleton] at hc
    rcases hc with rfl | rfl
    · simp [retainedBitDisagreementCoords, hbits.1]
    · simp [retainedBitDisagreementCoords, hbits.2]
  have hcard := Finset.card_le_card hsub
  have htwo : ({cf,cr} : Finset (Fin n)).card = 2 := by
    simp [hne]
  omega

#print axioms source_flip_target_active_bits_disagree
#print axioms forward_reverse_actual_collision_two_bridge_bit_disagreements
#print axioms forward_reverse_actual_collision_bridge_hamming_ge_two

end OrderedEdgeColoring
end JSP000404Research
