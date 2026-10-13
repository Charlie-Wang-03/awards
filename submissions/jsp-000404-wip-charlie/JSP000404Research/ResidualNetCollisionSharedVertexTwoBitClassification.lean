import JSP000404Research.ResidualNetCollisionCrossRoleEndpointSeparation
import Mathlib.Tactic

/-!
# Shared any original bridge vertex forces EXACTLY two source-bit flips

For any two DISTINCT genuine NET collisions hitting one canonical
diagonal, if their source-original SOFT bridges share ANY endpoint
(including a CROSS-ROLE lower=upper or upper=lower coincidence),
their sink words differ at EXACTLY TWO Boolean coordinates, not four.

The proof combines:
  (1) exact 2+2-support Hamming-vs-common-colour conservation;
  (2) positive Hamming distance for distinct subtype source words;
  (3) four-point original-bridge separation in the four-bit mode.

No AngleCap uniqueness, no payment, no alleged global injection.
-/

namespace JSP000404Research
namespace OrderedEdgeColoring

/-- The ACTUAL source diagonal collision's bridge endpoints share
a vertex IN ANY ROLE, including cross-role endpoint incidences. -/
def netCollisionBridgeOwnersShareVertex
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexp : ∀ v, exponent v ≤ n)
    (honeLoss : ∀ v, (active C v).card ≤ n - exponent v + 1)
    (s t : {w : Fin n → Bool //
      w ∈ netActualForwardReverseCollisionWords
        C exponent hexp honeLoss}) : Prop :=
  let bs := netCollisionCertifiedBridgeOwner C exponent hexp honeLoss s
  let bt := netCollisionCertifiedBridgeOwner C exponent hexp honeLoss t
  bs.1 = bt.1 ∨ bs.2 = bt.2 ∨ bs.1 = bt.2 ∨ bs.2 = bt.1

/-- If two DISTINCT genuine NET sources hit the SAME certified
diagonal and their original source bridges share ANY vertex, then
their source Hamming distance is exactly TWO, hence the canonical
original unordered transport colour pairs share exactly ONE colour. -/
theorem net_collision_shared_bridge_vertex_same_diagonal_distinct_sources_two_bit
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexp : ∀ v, exponent v ≤ n)
    (honeLoss : ∀ v, (active C v).card ≤ n - exponent v + 1)
    (s t : {w : Fin n → Bool //
      w ∈ netActualForwardReverseCollisionWords
        C exponent hexp honeLoss})
    (hne : s ≠ t)
    (hdiag : netCollisionCertifiedDiagonal C exponent hexp honeLoss s =
      netCollisionCertifiedDiagonal C exponent hexp honeLoss t)
    (hshare : netCollisionBridgeOwnersShareVertex
      C exponent hexp honeLoss s t) :
    (Finset.univ.filter (fun e : Fin n => s.1 e ≠ t.1 e)).card = 2 ∧
    (netCollisionCanonicalColourSupport C exponent hexp honeLoss s ∩
      netCollisionCanonicalColourSupport C exponent hexp honeLoss t).card = 1 := by
  classical
  let H : Finset (Fin n) :=
    Finset.univ.filter (fun e : Fin n => s.1 e ≠ t.1 e)
  have hpos : 0 < H.card := by
    by_contra hzero
    have hz : H.card = 0 := by omega
    have hnot : H = ∅ := Finset.card_eq_zero.mp hz
    have heq : s.1 = t.1 := by
      funext e
      by_contra he
      have hm : e ∈ H :=
        Finset.mem_filter.mpr ⟨Finset.mem_univ e, he⟩
      rw [hnot] at hm
      exact Finset.not_mem_empty e hm
    exact hne (Subtype.ext heq)
  have hfourNE : H.card ≠ 4 := by
    intro hfour
    have hsep :=
      net_collision_four_bit_same_diagonal_forces_four_distinct_bridge_vertices
        C exponent hexp honeLoss s t hdiag hfour
    rcases hsep with ⟨_, _, hll, huu, hlu, hul⟩
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
    · exact hll h
    · exact huu h
    · exact hlu h
    · exact hul h
  have hcount :=
    net_collision_equal_diagonal_hamming_plus_twice_common_eq_four
      C exponent hexp honeLoss s t hdiag
  change H.card +
    2 * (netCollisionCanonicalColourSupport C exponent hexp honeLoss s ∩
      netCollisionCanonicalColourSupport C exponent hexp honeLoss t).card = 4
    at hcount
  omega

#print axioms net_collision_shared_bridge_vertex_same_diagonal_distinct_sources_two_bit

end OrderedEdgeColoring
end JSP000404Research
