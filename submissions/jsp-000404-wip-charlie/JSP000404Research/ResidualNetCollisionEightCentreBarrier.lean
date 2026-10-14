import JSP000404Research.ResidualNetCollisionThreeColourTwoBitObstruction
import JSP000404Research.ResidualHardCarrierVertexMatching
import JSP000404Research.ResidualNetCollisionExactShellBipartiteCover
import Mathlib.Tactic

/-!
# Real NET duplicate-image debt requires at least eight original centres

Every genuine NET collision word has one original forward transportable
HARD carrier and one original reverse strict-descending RIGID HARD
carrier. The two classes are disjoint by the original safe outgoing
coordinate criterion. For two DISTINCT genuine NET sources with the
SAME canonical target d:

* their original forward HARD carriers differ, since equal carriers
  force equal upper endpoint-colour slots and hence equal source words;
* their original reverse HARD carriers differ, by the corresponding
  lower endpoint-colour slot injection;
* no forward HARD carrier is any reverse RIGID carrier, since safe
  outward transport is both true and false on such an edge.

Consequently four distinct HARD carriers exist. The already verified
global HARD carrier vertex matching uses TWO vertices PER carrier.
Thus a positive ACTUAL duplicate-image debt requires AT LEAST EIGHT
original vertices. The true geometric payment still has covered
diagonal blockers and other independent debts; this does not prove
JSP-000404.

Unlike a capacity min that rewrites to an old upper bound, this
eliminates the ACTUAL duplication term for all dimensions n when
the configuration has at most seven vertices.
-/

namespace JSP000404Research
namespace OrderedEdgeColoring

/-- Original hard pair of the unique actual forward hard source. -/
noncomputable def netCollisionForwardHardPair
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexp : ∀ v, exponent v ≤ n)
    (honeLoss : ∀ v, (active C v).card ≤ n - exponent v + 1)
    (s : {w : Fin n → Bool //
      w ∈ netActualForwardReverseCollisionWords
        C exponent hexp honeLoss}) : V × V :=
  (transportableWordCarrier C
    (netCollisionCertifiedForwardSource C exponent hexp honeLoss s)).1

/-- Original hard pair of the unique actual reverse rigid source. -/
noncomputable def netCollisionReverseHardPair
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexp : ∀ v, exponent v ≤ n)
    (honeLoss : ∀ v, (active C v).card ≤ n - exponent v + 1)
    (s : {w : Fin n → Bool //
      w ∈ netActualForwardReverseCollisionWords
        C exponent hexp honeLoss}) : V × V :=
  (strictDescentRigidWordCarrier C exponent
    (netCollisionCertifiedReverseSource C exponent hexp honeLoss s)).1

/-- All original forward pairs are genuine hard carriers with
an outward transport coordinate. -/
theorem net_collision_forward_hard_pair_safe
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexp : ∀ v, exponent v ≤ n)
    (honeLoss : ∀ v, (active C v).card ≤ n - exponent v + 1)
    (s : {w : Fin n → Bool //
      w ∈ netActualForwardReverseCollisionWords
        C exponent hexp honeLoss}) :
    netCollisionForwardHardPair C exponent hexp honeLoss s ∈
      hardOverlapCarrierPairs C ∧
    HasOutgoingHardTransport C
      (netCollisionForwardHardPair C exponent hexp honeLoss s).1
      (netCollisionForwardHardPair C exponent hexp honeLoss s).2 := by
  exact (mem_transportableHardOverlapCarrierPairs C _).mp
    (transportableWordCarrier C
      (netCollisionCertifiedForwardSource C exponent hexp honeLoss s)).2

/-- All reverse strict-descending hard pairs are hard carriers
WITHOUT an outward transport coordinate, so they are not
forward-transportable hard pairs. -/
theorem net_collision_reverse_hard_pair_rigid
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexp : ∀ v, exponent v ≤ n)
    (honeLoss : ∀ v, (active C v).card ≤ n - exponent v + 1)
    (s : {w : Fin n → Bool //
      w ∈ netActualForwardReverseCollisionWords
        C exponent hexp honeLoss}) :
    netCollisionReverseHardPair C exponent hexp honeLoss s ∈
      hardOverlapCarrierPairs C ∧
    ¬ HasOutgoingHardTransport C
      (netCollisionReverseHardPair C exponent hexp honeLoss s).1
      (netCollisionReverseHardPair C exponent hexp honeLoss s).2 := by
  have hr :=
    (mem_netStrictDescentRigidCarriers C exponent _).mp
      (strictDescentRigidWordCarrier C exponent
        (netCollisionCertifiedReverseSource C exponent hexp honeLoss s)).2
  have hr0 := (mem_netRigidHardCarriers C exponent _).mp hr.1
  exact ⟨(mem_netUnpaidHardCarrierPairs C exponent _).mp hr0.1 |>.1,
    hr0.2⟩

/-- Two distinct same-target NET sources cannot reuse the
same original FORWARD hard carrier. -/
theorem net_collision_distinct_same_target_forward_hard_pairs_ne
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexp : ∀ v, exponent v ≤ n)
    (honeLoss : ∀ v, (active C v).card ≤ n - exponent v + 1)
    (s t : {w : Fin n → Bool //
      w ∈ netActualForwardReverseCollisionWords
        C exponent hexp honeLoss})
    (hdiag : netCollisionCertifiedDiagonal C exponent hexp honeLoss s =
      netCollisionCertifiedDiagonal C exponent hexp honeLoss t)
    (hne : s ≠ t) :
    netCollisionForwardHardPair C exponent hexp honeLoss s ≠
      netCollisionForwardHardPair C exponent hexp honeLoss t := by
  intro hp
  have hv : (netCollisionForwardHardPair
      C exponent hexp honeLoss s).2 =
    (netCollisionForwardHardPair
      C exponent hexp honeLoss t).2 := by
    exact congrArg Prod.snd hp
  change (netCollisionCertifiedBridgeOwner
      C exponent hexp honeLoss s).2 =
    (netCollisionCertifiedBridgeOwner
      C exponent hexp honeLoss t).2 at hv
  have hcf :
      transportablePairColor C
        (transportableWordCarrier C
          (netCollisionCertifiedForwardSource C exponent hexp honeLoss s)) =
      transportablePairColor C
        (transportableWordCarrier C
          (netCollisionCertifiedForwardSource C exponent hexp honeLoss t)) :=
    congrArg (transportablePairColor C) (Subtype.ext hp)
  have hslot :
      netCollisionCertifiedUpperColourSlot C exponent hexp honeLoss s =
        netCollisionCertifiedUpperColourSlot C exponent hexp honeLoss t :=
    Prod.ext hv hcf
  exact hne (net_collision_same_target_upper_slot_injective
    C exponent hexp honeLoss s t hdiag hslot)

/-- Two distinct same-target NET sources cannot reuse the
same original REVERSE rigid hard carrier. -/
theorem net_collision_distinct_same_target_reverse_hard_pairs_ne
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexp : ∀ v, exponent v ≤ n)
    (honeLoss : ∀ v, (active C v).card ≤ n - exponent v + 1)
    (s t : {w : Fin n → Bool //
      w ∈ netActualForwardReverseCollisionWords
        C exponent hexp honeLoss})
    (hdiag : netCollisionCertifiedDiagonal C exponent hexp honeLoss s =
      netCollisionCertifiedDiagonal C exponent hexp honeLoss t)
    (hne : s ≠ t) :
    netCollisionReverseHardPair C exponent hexp honeLoss s ≠
      netCollisionReverseHardPair C exponent hexp honeLoss t := by
  intro hq
  have hb : (netCollisionReverseHardPair
      C exponent hexp honeLoss s).1 =
    (netCollisionReverseHardPair
      C exponent hexp honeLoss t).1 := by
    exact congrArg Prod.fst hq
  change (netCollisionCertifiedBridgeOwner
      C exponent hexp honeLoss s).1 =
    (netCollisionCertifiedBridgeOwner
      C exponent hexp honeLoss t).1 at hb
  have hcr :
      strictDescentRigidPairColor C exponent hexp honeLoss
        (strictDescentRigidWordCarrier C exponent
          (netCollisionCertifiedReverseSource C exponent hexp honeLoss s)) =
      strictDescentRigidPairColor C exponent hexp honeLoss
        (strictDescentRigidWordCarrier C exponent
          (netCollisionCertifiedReverseSource C exponent hexp honeLoss t)) :=
    congrArg (strictDescentRigidPairColor C exponent hexp honeLoss)
      (Subtype.ext hq)
  have hslot :
      netCollisionCertifiedLowerColourSlot C exponent hexp honeLoss s =
        netCollisionCertifiedLowerColourSlot C exponent hexp honeLoss t :=
    Prod.ext hb hcr
  exact hne (net_collision_same_target_lower_slot_injective
    C exponent hexp honeLoss s t hdiag hslot)

/-- A forward hard source pair and a reverse rigid hard source
pair can NEVER be the same pair, even across DIFFERENT genuine
NET collisions, by their conflicting safe-transport predicates. -/
theorem net_collision_forward_reverse_hard_pairs_ne
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexp : ∀ v, exponent v ≤ n)
    (honeLoss : ∀ v, (active C v).card ≤ n - exponent v + 1)
    (s t : {w : Fin n → Bool //
      w ∈ netActualForwardReverseCollisionWords
        C exponent hexp honeLoss}) :
    netCollisionForwardHardPair C exponent hexp honeLoss s ≠
      netCollisionReverseHardPair C exponent hexp honeLoss t := by
  intro heq
  have hs := (net_collision_forward_hard_pair_safe
      C exponent hexp honeLoss s).2
  have ht := (net_collision_reverse_hard_pair_rigid
      C exponent hexp honeLoss t).2
  exact ht (heq ▸ hs)

/-- Any two distinct ACTUAL NET same-target sources require
FOUR DISTINCT globally disjoint original hard carrier edges.
No false soft-edge/candidate ownership assumption is used. -/
theorem net_collision_two_same_target_sources_four_hard_carriers
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexp : ∀ v, exponent v ≤ n)
    (honeLoss : ∀ v, (active C v).card ≤ n - exponent v + 1)
    (s t : {w : Fin n → Bool //
      w ∈ netActualForwardReverseCollisionWords
        C exponent hexp honeLoss})
    (hdiag : netCollisionCertifiedDiagonal C exponent hexp honeLoss s =
      netCollisionCertifiedDiagonal C exponent hexp honeLoss t)
    (hne : s ≠ t) :
    4 ≤ (hardOverlapCarrierPairs C).card := by
  classical
  let ps := netCollisionForwardHardPair C exponent hexp honeLoss s
  let pt := netCollisionForwardHardPair C exponent hexp honeLoss t
  let qs := netCollisionReverseHardPair C exponent hexp honeLoss s
  let qt := netCollisionReverseHardPair C exponent hexp honeLoss t
  have hpst : ps ≠ pt :=
    net_collision_distinct_same_target_forward_hard_pairs_ne
      C exponent hexp honeLoss s t hdiag hne
  have hqst : qs ≠ qt :=
    net_collision_distinct_same_target_reverse_hard_pairs_ne
      C exponent hexp honeLoss s t hdiag hne
  have hpsqs : ps ≠ qs :=
    net_collision_forward_reverse_hard_pairs_ne
      C exponent hexp honeLoss s s
  have hpsqt : ps ≠ qt :=
    net_collision_forward_reverse_hard_pairs_ne
      C exponent hexp honeLoss s t
  have hptqs : pt ≠ qs :=
    net_collision_forward_reverse_hard_pairs_ne
      C exponent hexp honeLoss t s
  have hptqt : pt ≠ qt :=
    net_collision_forward_reverse_hard_pairs_ne
      C exponent hexp honeLoss t t
  have hsubset :
      ({ps,pt,qs,qt} : Finset (V × V)) ⊆ hardOverlapCarrierPairs C := by
    intro u hu
    simp only [Finset.mem_insert, Finset.mem_singleton] at hu
    rcases hu with rfl | rfl | rfl | rfl
    · exact (net_collision_forward_hard_pair_safe
        C exponent hexp honeLoss s).1
    · exact (net_collision_forward_hard_pair_safe
        C exponent hexp honeLoss t).1
    · exact (net_collision_reverse_hard_pair_rigid
        C exponent hexp honeLoss s).1
    · exact (net_collision_reverse_hard_pair_rigid
        C exponent hexp honeLoss t).1
  have hcard :
      ({ps,pt,qs,qt} : Finset (V × V)).card = 4 := by
    simp [hpst, hpsqs, hpsqt, hptqs, hptqt, hqst]
  have hle := Finset.card_le_card hsubset
  omega

/-- Positive genuine canonical duplicate debt FORCES at
least EIGHT original centres, for EVERY retained colour number n. -/
theorem net_collision_positive_duplicate_requires_eight_centres
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexp : ∀ v, exponent v ≤ n)
    (honeLoss : ∀ v, (active C v).card ≤ n - exponent v + 1)
    (hpositive : 0 < netCollisionCertifiedDuplicateDebt
      C exponent hexp honeLoss) :
    8 ≤ Fintype.card V := by
  obtain ⟨s,t,hne,hdiag⟩ :=
    net_collision_positive_duplicate_has_distinct_source_pair
      C exponent hexp honeLoss hpositive
  have hfour :=
    net_collision_two_same_target_sources_four_hard_carriers
      C exponent hexp honeLoss s t hdiag hne
  have hmatching :=
    hardOverlapCarrierPairs_two_mul_card_le_vertices C
  omega

/-- Genuine ACTUAL NET duplicate payment vanishes without any
additional AngleCap hypothesis if the original configuration has
at most SEVEN centres, regardless of n. This can remove one
real ledger debt in bounded-cardinality geometric subcases. -/
theorem net_collision_duplicate_debt_zero_of_at_most_seven_centres
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexp : ∀ v, exponent v ≤ n)
    (honeLoss : ∀ v, (active C v).card ≤ n - exponent v + 1)
    (hcard : Fintype.card V ≤ 7) :
    netCollisionCertifiedDuplicateDebt C exponent hexp honeLoss = 0 := by
  by_contra hnz
  have hp : 0 < netCollisionCertifiedDuplicateDebt
      C exponent hexp honeLoss := Nat.pos_of_ne_zero hnz
  have h8 :=
    net_collision_positive_duplicate_requires_eight_centres
      C exponent hexp honeLoss hp
  omega

/-- Exact mobile-hard ledger without a duplicate term whenever
the original residual colouring has at most SEVEN centres,
in EVERY Boolean dimension. -/
theorem net_mobile_mass_le_without_duplicates_of_at_most_seven_centres
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexp : ∀ v, exponent v ≤ n)
    (honeLoss : ∀ v, (active C v).card ≤ n - exponent v + 1)
    (hcard : Fintype.card V ≤ 7) :
    (netTransportableHardWords C exponent).card +
      (netStrictDescentRigidWords C exponent).card ≤
      (singletonCompletionWords C).card +
      (softOverlapCompletionWords C).card +
      ((Finset.univ : Finset (Fin n → Bool)) \
        coveredCompletionWords C).card +
      (netCollisionCertifiedCoveredDiagonals
        C exponent hexp honeLoss).card := by
  have hmobile :=
    net_mobile_mass_le_singleton_soft_holes_blockers_duplicates
      C exponent hexp honeLoss
  have hz :=
    net_collision_duplicate_debt_zero_of_at_most_seven_centres
      C exponent hexp honeLoss hcard
  omega

#print axioms net_collision_forward_hard_pair_safe
#print axioms net_collision_reverse_hard_pair_rigid
#print axioms net_collision_distinct_same_target_forward_hard_pairs_ne
#print axioms net_collision_distinct_same_target_reverse_hard_pairs_ne
#print axioms net_collision_forward_reverse_hard_pairs_ne
#print axioms net_collision_two_same_target_sources_four_hard_carriers
#print axioms net_collision_positive_duplicate_requires_eight_centres
#print axioms net_collision_duplicate_debt_zero_of_at_most_seven_centres
#print axioms net_mobile_mass_le_without_duplicates_of_at_most_seven_centres

end OrderedEdgeColoring
end JSP000404Research
