import JSP000404Research.ResidualNetActualCollisionLedger
import Mathlib.Tactic

/-!
# Actual opposite hard transport collisions require distinct flip colours

For a forward-transportable hard carrier p and a genuinely rigid
strict-descending hard carrier q, the source faces have disjoint
Boolean-word ownership. In particular, an actual forward/reverse
sink collision cannot arise by flipping the SAME retained coordinate:
the common target, flipped back at a common coordinate, would give
one original hard word owned by both p and q, contradicting
the hard-word-owner uniqueness and the rigid/no-forward dichotomy.

This gives a new concrete obstruction on the *actual* collision
set, not only its possible bridge-soft carrier geometry.
-/

namespace JSP000404Research
namespace OrderedEdgeColoring

/-- Source words from the forward-safe hard family and from the
terminal strict-rigid hard family can never be identical. -/
theorem forward_hard_source_ne_reverse_strict_source
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (x : {word : Fin n → Bool //
      word ∈ transportableHardOverlapCompletionWords C})
    (y : {word : Fin n → Bool //
      word ∈ netStrictDescentRigidWords C exponent}) :
    x.1 ≠ y.1 := by
  intro heq
  let p := transportableWordCarrier C x
  let q := strictDescentRigidWordCarrier C exponent y
  have hp : p.1 ∈ hardOverlapCarrierPairs C :=
    ((mem_transportableHardOverlapCarrierPairs C p.1).1 p.2).1
  have hforward : HasOutgoingHardTransport C p.1.1 p.1.2 :=
    ((mem_transportableHardOverlapCarrierPairs C p.1).1 p.2).2
  have hqdata := (mem_netStrictDescentRigidCarriers C exponent q.1).1 q.2
  have hqrig := (mem_netRigidHardCarriers C exponent q.1).1 hqdata.1
  have hq : q.1 ∈ hardOverlapCarrierPairs C :=
    ((mem_netUnpaidHardCarrierPairs C exponent q.1).1 hqrig.1).1
  have hr : ¬ HasOutgoingHardTransport C q.1.1 q.1.2 := hqrig.2
  have hpword := transportableWordCarrier_covers C x
  have hqword := strictDescentRigidWordCarrier_covers C exponent y
  have howner : p.1 = q.1 := by
    apply hard_carrier_word_owner_unique C hp hq
      (Finset.mem_inter.mpr
        ⟨(Finset.mem_inter.mp hpword).1,
          (Finset.mem_inter.mp hpword).2⟩)
    rw [heq]
    exact hqword
  have hforward' : HasOutgoingHardTransport C q.1.1 q.1.2 := by
    simpa only [howner] using hforward
  exact hr hforward'

/-- Genuine collision between full forward and reverse strict-rigid
one-bit maps FORCES distinct flipped retained coordinates. -/
theorem forward_reverse_actual_collision_distinct_flip_colors
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
    transportablePairColor C (transportableWordCarrier C x) ≠
      strictDescentRigidPairColor C exponent hexp honeLoss
        (strictDescentRigidWordCarrier C exponent y) := by
  intro hcol
  have hsource :
      x.1 = y.1 := by
    apply flipCompletionWord_injective
      (transportablePairColor C (transportableWordCarrier C x))
    change flipCompletionWord
      (transportablePairColor C (transportableWordCarrier C x)) x.1 =
      flipCompletionWord
      (strictDescentRigidPairColor C exponent hexp honeLoss
        (strictDescentRigidWordCarrier C exponent y)) y.1
      at hcollision
    rw [hcol] at hcollision
    exact hcollision
  exact forward_hard_source_ne_reverse_strict_source
    C exponent x y hsource

#print axioms forward_hard_source_ne_reverse_strict_source
#print axioms forward_reverse_actual_collision_distinct_flip_colors

end OrderedEdgeColoring
end JSP000404Research
