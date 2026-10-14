import JSP000404Research.ResidualNetCollisionVertexBudgetFibre
import JSP000404Research.ResidualNetCollisionSharedVertexTwoBitClassification
import Mathlib.Tactic

/-!
# ALL same-target NET duplicate soft bridges have four distinct endpoints

A previous four-bit result only obtained bridge-vertex separation
under the Hamming-four/disjoint-colour hypothesis. But original
forward/reverse HARD carriers are globally vertex-disjoint:

* Same-target DISTINCT NET sources own distinct forward hard carriers.
* They also own distinct reverse rigid hard carriers.
* Forward hard and reverse rigid carriers are ALWAYS different.
* No distinct hard carriers share ANY original vertex.

Thus the two source-induced SOFT bridge owners share no endpoint
whatsoever, EVEN WHEN the sources differ at only TWO bits.

For n=3, every positive duplicate target debt consequently has
a two-bit/single-shared-flip-colour witness whose TWO SOFT bridges
have FOUR DISTINCT ORIGINAL VERTICES. The old "shared bridge
vertex => two bits" alternative is genuinely eliminated in the
actual NET source category.

This is a nonvacuous obstruction-case reduction, not a payment
from true Boolean holes or unreserved dyadic surplus.
-/

namespace JSP000404Research
namespace OrderedEdgeColoring

/-- A direct usable four-way endpoint version of the previously
proved global HARD-carrier vertex matching. -/
theorem distinct_hard_carriers_all_four_endpoint_inequalities
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (p q : V × V)
    (hp : p ∈ hardOverlapCarrierPairs C)
    (hq : q ∈ hardOverlapCarrierPairs C)
    (hne : p ≠ q) :
    p.1 ≠ q.1 ∧ p.1 ≠ q.2 ∧ p.2 ≠ q.1 ∧ p.2 ≠ q.2 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro h
    exact hne (hard_carrier_shared_endpoint_implies_same_pair
      C hp hq (Or.inl h))
  · intro h
    exact hne (hard_carrier_shared_endpoint_implies_same_pair
      C hp hq (Or.inr (Or.inl h)))
  · intro h
    exact hne (hard_carrier_shared_endpoint_implies_same_pair
      C hp hq (Or.inr (Or.inr (Or.inl h))))
  · intro h
    exact hne (hard_carrier_shared_endpoint_implies_same_pair
      C hp hq (Or.inr (Or.inr (Or.inr h))))

/-- For distinct ACTUAL NET hard-source collisions with the
same target, their two ORIGINAL SOFT bridge owners are entirely
vertex-disjoint, independent of whether their Hamming distance
is TWO or FOUR.

The four combinations include cross roles: lower(s) != upper(t)
and upper(s) != lower(t). -/
theorem net_collision_distinct_same_target_soft_bridges_four_vertices
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
    (netCollisionCertifiedBridgeOwner C exponent hexp honeLoss s).1 ≠
      (netCollisionCertifiedBridgeOwner C exponent hexp honeLoss t).1 ∧
    (netCollisionCertifiedBridgeOwner C exponent hexp honeLoss s).2 ≠
      (netCollisionCertifiedBridgeOwner C exponent hexp honeLoss t).2 ∧
    (netCollisionCertifiedBridgeOwner C exponent hexp honeLoss s).1 ≠
      (netCollisionCertifiedBridgeOwner C exponent hexp honeLoss t).2 ∧
    (netCollisionCertifiedBridgeOwner C exponent hexp honeLoss s).2 ≠
      (netCollisionCertifiedBridgeOwner C exponent hexp honeLoss t).1 := by
  let ps := netCollisionForwardHardPair C exponent hexp honeLoss s
  let pt := netCollisionForwardHardPair C exponent hexp honeLoss t
  let qs := netCollisionReverseHardPair C exponent hexp honeLoss s
  let qt := netCollisionReverseHardPair C exponent hexp honeLoss t
  have hps : ps ∈ hardOverlapCarrierPairs C :=
    (net_collision_forward_hard_pair_safe C exponent hexp honeLoss s).1
  have hpt : pt ∈ hardOverlapCarrierPairs C :=
    (net_collision_forward_hard_pair_safe C exponent hexp honeLoss t).1
  have hqs : qs ∈ hardOverlapCarrierPairs C :=
    (net_collision_reverse_hard_pair_rigid C exponent hexp honeLoss s).1
  have hqt : qt ∈ hardOverlapCarrierPairs C :=
    (net_collision_reverse_hard_pair_rigid C exponent hexp honeLoss t).1
  have hpspt : ps ≠ pt :=
    net_collision_distinct_same_target_forward_hard_pairs_ne
      C exponent hexp honeLoss s t hdiag hne
  have hqsqt : qs ≠ qt :=
    net_collision_distinct_same_target_reverse_hard_pairs_ne
      C exponent hexp honeLoss s t hdiag hne
  have hqspt : qs ≠ pt :=
    (net_collision_forward_reverse_hard_pairs_ne
      C exponent hexp honeLoss t s).symm
  have hpsqt : ps ≠ qt :=
    net_collision_forward_reverse_hard_pairs_ne
      C exponent hexp honeLoss s t
  have hrr := distinct_hard_carriers_all_four_endpoint_inequalities
    C qs qt hqs hqt hqsqt
  have hff := distinct_hard_carriers_all_four_endpoint_inequalities
    C ps pt hps hpt hpspt
  have hrf := distinct_hard_carriers_all_four_endpoint_inequalities
    C qs pt hqs hpt hqspt
  have hfr := distinct_hard_carriers_all_four_endpoint_inequalities
    C ps qt hps hqt hpsqt
  change qs.1 ≠ qt.1 ∧ ps.2 ≠ pt.2 ∧
    qs.1 ≠ pt.2 ∧ ps.2 ≠ qt.1
  exact ⟨hrr.1, hff.2.2.2, hrf.2.1, hfr.2.2.1⟩

/-- The "shared any original bridge endpoint" subcase
does not occur for DISTINCT ACTUAL same-target sources,
even in the two-bit Hamming alternative. -/
theorem net_collision_distinct_same_target_no_shared_soft_bridge_vertex
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
    ¬ netCollisionBridgeOwnersShareVertex
      C exponent hexp honeLoss s t := by
  intro hshare
  have hsep :=
    net_collision_distinct_same_target_soft_bridges_four_vertices
      C exponent hexp honeLoss s t hdiag hne
  change
    (netCollisionCertifiedBridgeOwner C exponent hexp honeLoss s).1 =
      (netCollisionCertifiedBridgeOwner C exponent hexp honeLoss t).1 ∨
    (netCollisionCertifiedBridgeOwner C exponent hexp honeLoss s).2 =
      (netCollisionCertifiedBridgeOwner C exponent hexp honeLoss t).2 ∨
    (netCollisionCertifiedBridgeOwner C exponent hexp honeLoss s).1 =
      (netCollisionCertifiedBridgeOwner C exponent hexp honeLoss t).2 ∨
    (netCollisionCertifiedBridgeOwner C exponent hexp honeLoss s).2 =
      (netCollisionCertifiedBridgeOwner C exponent hexp honeLoss t).1
    at hshare
  rcases hshare with h | h | h | h
  · exact hsep.1 h
  · exact hsep.2.1 h
  · exact hsep.2.2.1 h
  · exact hsep.2.2.2 h

/-- n<=3: positive ACTUAL NET duplicate debt only survives as a
two-bit collision between two ENTIRELY VERTEX-DISJOINT original
soft bridges whose flip-supports share exactly ONE colour. -/
theorem net_collision_positive_duplicate_three_colours_forces_disjoint_bridges
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexp : ∀ v, exponent v ≤ n)
    (honeLoss : ∀ v, (active C v).card ≤ n - exponent v + 1)
    (hn : n ≤ 3)
    (hpositive : 0 <
      netCollisionCertifiedDuplicateDebt C exponent hexp honeLoss) :
    ∃ s t : {w : Fin n → Bool //
        w ∈ netActualForwardReverseCollisionWords
          C exponent hexp honeLoss},
      s ≠ t ∧
      netCollisionCertifiedDiagonal C exponent hexp honeLoss s =
        netCollisionCertifiedDiagonal C exponent hexp honeLoss t ∧
      (Finset.univ.filter (fun i : Fin n => s.1 i ≠ t.1 i)).card = 2 ∧
      (netCollisionCanonicalColourSupport C exponent hexp honeLoss s ∩
        netCollisionCanonicalColourSupport C exponent hexp honeLoss t).card = 1 ∧
      ¬ netCollisionBridgeOwnersShareVertex
        C exponent hexp honeLoss s t := by
  obtain ⟨s, t, hne, hdiag, _, htwo, hcommon⟩ :=
    net_collision_positive_duplicate_n_le_three_forces_two_bits_one_common
      C exponent hexp honeLoss hn hpositive
  refine ⟨s, t, hne, hdiag, htwo, hcommon, ?_⟩
  exact net_collision_distinct_same_target_no_shared_soft_bridge_vertex
    C exponent hexp honeLoss s t hdiag hne

#print axioms distinct_hard_carriers_all_four_endpoint_inequalities
#print axioms net_collision_distinct_same_target_soft_bridges_four_vertices
#print axioms net_collision_distinct_same_target_no_shared_soft_bridge_vertex
#print axioms net_collision_positive_duplicate_three_colours_forces_disjoint_bridges

end OrderedEdgeColoring
end JSP000404Research
