import JSP000404Research.ResidualActualCollisionDistinctFlip
import Mathlib.Tactic

/-!
# Actual opposite hard-flip collisions force incomparable active supports

Suppose two globally verified hard-face flip transports collide:
a forward-mobile hard source on p=(a,v) and a strictly descending
reverse-rigid hard source on q=(b,z).

The image belongs simultaneously to Q_v and Q_b, i.e. the SOFT bridge
cube with oriented endpoints (b,v). The forward flip colour is active
at a, inactive at v. Were it also inactive at b, the original
forward HARD source word would lie simultaneously in Q_a, Q_v and
Q_b, contradicting certified maximum completion multiplicity two.

Dually, the reverse flip colour is active at z, inactive at b.
Were it also inactive at v, the reverse HARD source word would
lie simultaneously in Q_b, Q_z and Q_v, equally impossible.

Consequently the retained-active palettes at b and v are
INCOMPARABLE, not just distinct. A soft candidate bridge carrier
with nested active palettes CANNOT host any actual cross-image
collision. This is a genuine structural exclusion beyond the
previous coarse possible-bridge pool; no true-hole or profile-surplus
payment is asserted.
-/

namespace JSP000404Research
namespace OrderedEdgeColoring

/-- The two opposite hard classes have no shared carrier vertex.
The final three pairwise inequalities are exactly those needed for
the no-three-completion argument on either transported source. -/
theorem forward_reverse_hard_source_critical_vertices_distinct
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (x : {word : Fin n → Bool //
      word ∈ transportableHardOverlapCompletionWords C})
    (y : {word : Fin n → Bool //
      word ∈ netStrictDescentRigidWords C exponent}) :
    let p := transportableWordCarrier C x
    let q := strictDescentRigidWordCarrier C exponent y
    p.1.1 ≠ q.1.1 ∧
      p.1.2 ≠ q.1.1 ∧
        q.1.2 ≠ p.1.2 := by
  let p := transportableWordCarrier C x
  let q := strictDescentRigidWordCarrier C exponent y
  have hpInfo := (mem_transportableHardOverlapCarrierPairs C p.1).1 p.2
  have hqInfo := (mem_netStrictDescentRigidCarriers C exponent q.1).1 q.2
  have hqRigid := (mem_netRigidHardCarriers C exponent q.1).1 hqInfo.1
  have hqHard : q.1 ∈ hardOverlapCarrierPairs C :=
    ((mem_netUnpaidHardCarrierPairs C exponent q.1).1 hqRigid.1).1
  have hneq : p.1 ≠ q.1 := by
    intro heq
    have hforward : HasOutgoingHardTransport C q.1.1 q.1.2 := by
      simpa only [heq] using hpInfo.2
    exact hqRigid.2 hforward
  have hunique := hard_carrier_shared_endpoint_implies_same_pair
    C hpInfo.1 hqHard
  refine ⟨?_, ?_, ?_⟩
  · intro heq
    exact hneq (hunique (Or.inl heq))
  · intro heq
    exact hneq (hunique (Or.inr (Or.inr (Or.inl heq))))
  · intro heq
    exact hneq (hunique (Or.inr (Or.inr (Or.inr heq.symm))))

/-- Both hard flip coordinates MUST be active at the opposite
bridge endpoint, since otherwise the ORIGINAL hard source word
would be covered by three distinct centres. -/
theorem forward_reverse_collision_cross_active_flip_colors
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
    transportablePairColor C p ∈ retainedActive C q.1.1 ∧
      strictDescentRigidPairColor C exponent hexp honeLoss q ∈
        retainedActive C p.1.2 := by
  classical
  let p := transportableWordCarrier C x
  let q := strictDescentRigidWordCarrier C exponent y
  let cf := transportablePairColor C p
  let cr := strictDescentRigidPairColor C exponent hexp honeLoss q
  have hdisj :=
    forward_reverse_hard_source_critical_vertices_distinct
      C exponent x y
  change p.1.1 ≠ q.1.1 ∧ p.1.2 ≠ q.1.1 ∧
      q.1.2 ≠ p.1.2 at hdisj
  have hpOrder := (transportableWordCarrier_residual C x).1
  have hqOrder := (strictDescentRigidWordCarrier_residual C exponent y).1
  have hxp := Finset.mem_inter.mp
    (transportableWordCarrier_covers C x)
  have hyq := Finset.mem_inter.mp
    (strictDescentRigidWordCarrier_covers C exponent y)
  constructor
  · by_contra hcNot
    have hwQ :
        (transportableHardWordToSingletonOrSoft C x).1 ∈
          retainedCompletionWords C q.1.1 := by
      rw [hcollision]
      exact strictDescentRigidWordToSingletonOrSoft_mem_lower
        C exponent hexp honeLoss y
    have hxQ : x.1 ∈ retainedCompletionWords C q.1.1 := by
      have hflipped : flipCompletionWord cf x.1 ∈
          retainedCompletionWords C q.1.1 := hwQ
      have hback :=
        flipCompletionWord_mem_upper_of_inactive C hcNot hflipped
      simpa only [flipCompletionWord_flip] using hback
    exact no_three_distinct_share_retained_completion
      C (ne_of_lt hpOrder) hdisj.1 hdisj.2.1
      hxp.1 hxp.2 hxQ
  · by_contra hcNot
    have hwP :
        (strictDescentRigidWordToSingletonOrSoft
          C exponent hexp honeLoss y).1 ∈
          retainedCompletionWords C p.1.2 := by
      rw [← hcollision]
      exact transportableHardWordToSingletonOrSoft_mem_upper C x
    have hyP : y.1 ∈ retainedCompletionWords C p.1.2 := by
      have hflipped : flipCompletionWord cr y.1 ∈
          retainedCompletionWords C p.1.2 := hwP
      have hback :=
        flipCompletionWord_mem_upper_of_inactive C hcNot hflipped
      simpa only [flipCompletionWord_flip] using hback
    exact no_three_distinct_share_retained_completion
      C (ne_of_lt hqOrder) hdisj.2.1.symm hdisj.2.2
      hyq.1 hyq.2 hyP

/-- A genuine collision bridge (reverse lower, forward upper)
has INCOMPARABLE retained-active palettes. Hence nested palettes
exclude actual collisions, even if a complete SOFT bridge face
exists as a hypothetical overlap. -/
theorem forward_reverse_collision_bridge_active_incomparable
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
    ¬ retainedActive C q.1.1 ⊆ retainedActive C p.1.2 ∧
      ¬ retainedActive C p.1.2 ⊆ retainedActive C q.1.1 := by
  let p := transportableWordCarrier C x
  let q := strictDescentRigidWordCarrier C exponent y
  have hcross :=
    forward_reverse_collision_cross_active_flip_colors
      C exponent hexp honeLoss x y hcollision
  change transportablePairColor C p ∈ retainedActive C q.1.1 ∧
    strictDescentRigidPairColor C exponent hexp honeLoss q ∈
      retainedActive C p.1.2 at hcross
  have hfInactive := (transportablePairColor_spec C p).2
  have hrInactive :=
    (strictDescentRigidPairColor_spec C exponent hexp honeLoss q).2
  constructor
  · intro hsub
    exact hfInactive (hsub hcross.1)
  · intro hsub
    exact hrInactive (hsub hcross.2)

#print axioms forward_reverse_hard_source_critical_vertices_distinct
#print axioms forward_reverse_collision_cross_active_flip_colors
#print axioms forward_reverse_collision_bridge_active_incomparable

end OrderedEdgeColoring
end JSP000404Research
