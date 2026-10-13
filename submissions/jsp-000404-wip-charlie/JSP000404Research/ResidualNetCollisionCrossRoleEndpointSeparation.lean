import JSP000404Research.ResidualNetCollisionFourBitBridgeEndpointSeparation
import Mathlib.Tactic

/-!
# Four-bit canonical diagonal reuse forces four pairwise distinct soft-bridge endpoints

The previous proof only ruled out shared endpoints in the SAME roles.
In fact the precise target-dependent singleton active-violation sets
also rule out CROSS-role equalities: a lower endpoint of one NET
collision cannot equal the upper endpoint of another four-bit
same-target collision, since the corresponding original forward
and reverse flip colours would then have to agree.

Consequently genuine four-bit same-diagonal source duplication
requires all FOUR actual original soft bridge vertices to be pairwise
distinct, including cross-role coincidences. This is a stronger
source-native necessary condition; it is NOT a planar AngleCap
exclusion or a payment of the actual duplicate-image debt.
-/

namespace JSP000404Research
namespace OrderedEdgeColoring

/-- The original FORWARD flip of s agrees with the original REVERSE
flip of t if both genuine collisions have the same canonical
diagonal and lower(s)=upper(t). This is a CROSS-ROLE endpoint law. -/
theorem net_collision_same_diagonal_lower_eq_other_upper_forces_cross_colour
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
    (hvertex :
      (netCollisionCertifiedBridgeOwner C exponent hexp honeLoss s).1 =
      (netCollisionCertifiedBridgeOwner C exponent hexp honeLoss t).2) :
    transportablePairColor C
      (transportableWordCarrier C
        (netCollisionCertifiedForwardSource C exponent hexp honeLoss s)) =
    strictDescentRigidPairColor C exponent hexp honeLoss
      (strictDescentRigidWordCarrier C exponent
        (netCollisionCertifiedReverseSource C exponent hexp honeLoss t)) := by
  classical
  let xS := netCollisionCertifiedForwardSource C exponent hexp honeLoss s
  let yS := netCollisionCertifiedReverseSource C exponent hexp honeLoss s
  let xT := netCollisionCertifiedForwardSource C exponent hexp honeLoss t
  let yT := netCollisionCertifiedReverseSource C exponent hexp honeLoss t
  let pS := transportableWordCarrier C xS
  let qS := strictDescentRigidWordCarrier C exponent yS
  let pT := transportableWordCarrier C xT
  let qT := strictDescentRigidWordCarrier C exponent yT
  let cfS := transportablePairColor C pS
  let crT := strictDescentRigidPairColor C exponent hexp honeLoss qT
  have hS := net_collision_certified_diagonal_exact_two_endpoint_shells
    C exponent hexp honeLoss s
  have hT := net_collision_certified_diagonal_exact_two_endpoint_shells
    C exponent hexp honeLoss t
  change retainedActiveViolationCoords C qS.1.1
      (netCollisionCertifiedDiagonal C exponent hexp honeLoss s) =
      {cfS} ∧
    retainedActiveViolationCoords C pS.1.2
      (netCollisionCertifiedDiagonal C exponent hexp honeLoss s) = _ at hS
  change retainedActiveViolationCoords C qT.1.1
      (netCollisionCertifiedDiagonal C exponent hexp honeLoss t) = _ ∧
    retainedActiveViolationCoords C pT.1.2
      (netCollisionCertifiedDiagonal C exponent hexp honeLoss t) =
      {crT} at hT
  have hb : qS.1.1 = pT.1.2 := hvertex
  have hsets : ({cfS} : Finset (Fin n)) = {crT} := calc
    ({cfS} : Finset (Fin n)) =
      retainedActiveViolationCoords C qS.1.1
        (netCollisionCertifiedDiagonal C exponent hexp honeLoss s) := hS.1.symm
    _ = retainedActiveViolationCoords C pT.1.2
        (netCollisionCertifiedDiagonal C exponent hexp honeLoss t) := by
      rw [hb, hdiag]
    _ = {crT} := hT.2
  have hm : cfS ∈ ({crT} : Finset (Fin n)) := by
    rw [← hsets]
    simp
  exact Finset.mem_singleton.mp hm

/-- The other CROSS-ROLE equality upper(s)=lower(t) likewise
forces reverse(s)=forward(t) as original actual flip colours. -/
theorem net_collision_same_diagonal_upper_eq_other_lower_forces_cross_colour
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
    (hvertex :
      (netCollisionCertifiedBridgeOwner C exponent hexp honeLoss s).2 =
      (netCollisionCertifiedBridgeOwner C exponent hexp honeLoss t).1) :
    strictDescentRigidPairColor C exponent hexp honeLoss
      (strictDescentRigidWordCarrier C exponent
        (netCollisionCertifiedReverseSource C exponent hexp honeLoss s)) =
    transportablePairColor C
      (transportableWordCarrier C
        (netCollisionCertifiedForwardSource C exponent hexp honeLoss t)) := by
  exact (net_collision_same_diagonal_lower_eq_other_upper_forces_cross_colour
    C exponent hexp honeLoss t s hdiag.symm hvertex.symm).symm

/-- Each genuine original bridge has DISTINCT lower and upper
vertices, derived from its two distinct hard flip colours and exact
single-coordinate diagonal constraint violations, independently of
any further global AngleCap payment. -/
theorem net_collision_original_soft_bridge_endpoints_distinct
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexp : ∀ v, exponent v ≤ n)
    (honeLoss : ∀ v, (active C v).card ≤ n - exponent v + 1)
    (s : {w : Fin n → Bool //
      w ∈ netActualForwardReverseCollisionWords
        C exponent hexp honeLoss}) :
    (netCollisionCertifiedBridgeOwner C exponent hexp honeLoss s).1 ≠
      (netCollisionCertifiedBridgeOwner C exponent hexp honeLoss s).2 := by
  intro heq
  have hcol := net_collision_same_diagonal_lower_eq_other_upper_forces_cross_colour
    C exponent hexp honeLoss s s rfl heq
  exact (net_collision_certified_forward_reverse_colours_distinct
    C exponent hexp honeLoss s) hcol

/-- Strengthens the prior SAME-ROLE separation: FOUR-bit same-target
repetition requires all FOUR source-native original soft-bridge
endpoints to be pairwise distinct, including CROSS-role intersections. -/
theorem net_collision_four_bit_same_diagonal_forces_four_distinct_bridge_vertices
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
    (hfour : (Finset.univ.filter
      (fun e : Fin n => s.1 e ≠ t.1 e)).card = 4) :
    let bs := netCollisionCertifiedBridgeOwner C exponent hexp honeLoss s
    let bt := netCollisionCertifiedBridgeOwner C exponent hexp honeLoss t
    bs.1 ≠ bs.2 ∧ bt.1 ≠ bt.2 ∧
      bs.1 ≠ bt.1 ∧ bs.2 ≠ bt.2 ∧
      bs.1 ≠ bt.2 ∧ bs.2 ≠ bt.1 := by
  classical
  let bs := netCollisionCertifiedBridgeOwner C exponent hexp honeLoss s
  let bt := netCollisionCertifiedBridgeOwner C exponent hexp honeLoss t
  change bs.1 ≠ bs.2 ∧ bt.1 ≠ bt.2 ∧
      bs.1 ≠ bt.1 ∧ bs.2 ≠ bt.2 ∧
      bs.1 ≠ bt.2 ∧ bs.2 ≠ bt.1
  have hsame :=
    net_collision_four_bit_same_diagonal_forces_both_bridge_endpoints_distinct
      C exponent hexp honeLoss s t hdiag hfour
  have hdis :=
    (net_collision_equal_diagonal_four_bits_iff_disjoint_colours
      C exponent hexp honeLoss s t hdiag).mp hfour
  have hdis' := Finset.disjoint_left.mp hdis
  have hcrossOne : bs.1 ≠ bt.2 := by
    intro heq
    have hc := net_collision_same_diagonal_lower_eq_other_upper_forces_cross_colour
      C exponent hexp honeLoss s t hdiag heq
    have hmemS :
        transportablePairColor C
          (transportableWordCarrier C
            (netCollisionCertifiedForwardSource C exponent hexp honeLoss s)) ∈
        netCollisionCanonicalColourSupport C exponent hexp honeLoss s := by
      simp [netCollisionCanonicalColourSupport]
    have hmemT :
        transportablePairColor C
          (transportableWordCarrier C
            (netCollisionCertifiedForwardSource C exponent hexp honeLoss s)) ∈
        netCollisionCanonicalColourSupport C exponent hexp honeLoss t := by
      simp [netCollisionCanonicalColourSupport, hc]
    exact hdis' hmemS hmemT
  have hcrossTwo : bs.2 ≠ bt.1 := by
    intro heq
    have hc := net_collision_same_diagonal_upper_eq_other_lower_forces_cross_colour
      C exponent hexp honeLoss s t hdiag heq
    have hmemS :
        strictDescentRigidPairColor C exponent hexp honeLoss
          (strictDescentRigidWordCarrier C exponent
            (netCollisionCertifiedReverseSource C exponent hexp honeLoss s)) ∈
        netCollisionCanonicalColourSupport C exponent hexp honeLoss s := by
      simp [netCollisionCanonicalColourSupport]
    have hmemT :
        strictDescentRigidPairColor C exponent hexp honeLoss
          (strictDescentRigidWordCarrier C exponent
            (netCollisionCertifiedReverseSource C exponent hexp honeLoss s)) ∈
        netCollisionCanonicalColourSupport C exponent hexp honeLoss t := by
      simp [netCollisionCanonicalColourSupport, hc]
    exact hdis' hmemS hmemT
  exact ⟨net_collision_original_soft_bridge_endpoints_distinct
       C exponent hexp honeLoss s,
    net_collision_original_soft_bridge_endpoints_distinct
       C exponent hexp honeLoss t,
    hsame.1, hsame.2, hcrossOne, hcrossTwo⟩

#print axioms net_collision_same_diagonal_lower_eq_other_upper_forces_cross_colour
#print axioms net_collision_same_diagonal_upper_eq_other_lower_forces_cross_colour
#print axioms net_collision_original_soft_bridge_endpoints_distinct
#print axioms net_collision_four_bit_same_diagonal_forces_four_distinct_bridge_vertices

end OrderedEdgeColoring
end JSP000404Research
