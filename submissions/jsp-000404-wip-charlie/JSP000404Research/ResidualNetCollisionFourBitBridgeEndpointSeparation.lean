import JSP000404Research.ResidualNetCollisionTargetShellBridgeFibre
import JSP000404Research.ResidualNetCollisionSupportOverlapLaw
import Mathlib.Tactic

/-!
# Shared original soft bridge endpoints force shared ORIGINAL flip colours

Exact one-bit active violation sets provide a new across-bridge
rigidity theorem: if two actual NET collisions have the SAME canonical
diagonal AND the SAME reverse-lower bridge endpoint, their original
FORWARD flip colours are equal. If they have the SAME forward-upper
bridge endpoint, their original REVERSE flip colours are equal.

Combining this with the earlier exact 4-bit-vs-disjoint-colour law
shows any FOUR-bit duplicate-diagonal source pair has to come from
bridges with BOTH endpoints distinct.

Thus across-bridge target duplication subdivides honestly into
(1) two-bit shared-vertex or fully separate-vertex modes, and
(2) four-bit strictly endpoint-disjoint modes.
No automatic AngleCap exclusion or global payment is asserted.
-/

namespace JSP000404Research
namespace OrderedEdgeColoring

/-- Equal canonical diagonals and the SAME reverse-lower soft
bridge endpoint FORCE equality of ORIGINAL forward flip colours,
even when the forward hard carriers/upper endpoints differ. -/
theorem net_collision_equal_diagonal_same_lower_forward_colour_eq
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
    (hlower :
      (netCollisionCertifiedBridgeOwner C exponent hexp honeLoss s).1 =
      (netCollisionCertifiedBridgeOwner C exponent hexp honeLoss t).1) :
    transportablePairColor C
      (transportableWordCarrier C
        (netCollisionCertifiedForwardSource C exponent hexp honeLoss s)) =
    transportablePairColor C
      (transportableWordCarrier C
        (netCollisionCertifiedForwardSource C exponent hexp honeLoss t)) := by
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
  let cfT := transportablePairColor C pT
  let crS := strictDescentRigidPairColor C exponent hexp honeLoss qS
  let crT := strictDescentRigidPairColor C exponent hexp honeLoss qT
  have hS := net_collision_certified_diagonal_exact_two_endpoint_shells
    C exponent hexp honeLoss s
  have hT := net_collision_certified_diagonal_exact_two_endpoint_shells
    C exponent hexp honeLoss t
  change retainedActiveViolationCoords C qS.1.1
      (netCollisionCertifiedDiagonal C exponent hexp honeLoss s) =
      {cfS} ∧
    retainedActiveViolationCoords C pS.1.2
      (netCollisionCertifiedDiagonal C exponent hexp honeLoss s) =
      {crS} at hS
  change retainedActiveViolationCoords C qT.1.1
      (netCollisionCertifiedDiagonal C exponent hexp honeLoss t) =
      {cfT} ∧
    retainedActiveViolationCoords C pT.1.2
      (netCollisionCertifiedDiagonal C exponent hexp honeLoss t) =
      {crT} at hT
  have hb : qS.1.1 = qT.1.1 := hlower
  have hsets : ({cfS} : Finset (Fin n)) = {cfT} := calc
    ({cfS} : Finset (Fin n)) =
      retainedActiveViolationCoords C qS.1.1
        (netCollisionCertifiedDiagonal C exponent hexp honeLoss s) := hS.1.symm
    _ = retainedActiveViolationCoords C qT.1.1
        (netCollisionCertifiedDiagonal C exponent hexp honeLoss t) := by
      rw [hb, hdiag]
    _ = {cfT} := hT.1
  have hm : cfS ∈ ({cfT} : Finset (Fin n)) := by
    rw [← hsets]
    simp
  exact Finset.mem_singleton.mp hm

/-- Equal canonical diagonals and the SAME forward-upper soft
bridge endpoint FORCE equality of ORIGINAL reverse flip colours. -/
theorem net_collision_equal_diagonal_same_upper_reverse_colour_eq
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
    (hupper :
      (netCollisionCertifiedBridgeOwner C exponent hexp honeLoss s).2 =
      (netCollisionCertifiedBridgeOwner C exponent hexp honeLoss t).2) :
    strictDescentRigidPairColor C exponent hexp honeLoss
      (strictDescentRigidWordCarrier C exponent
        (netCollisionCertifiedReverseSource C exponent hexp honeLoss s)) =
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
  let cfT := transportablePairColor C pT
  let crS := strictDescentRigidPairColor C exponent hexp honeLoss qS
  let crT := strictDescentRigidPairColor C exponent hexp honeLoss qT
  have hS := net_collision_certified_diagonal_exact_two_endpoint_shells
    C exponent hexp honeLoss s
  have hT := net_collision_certified_diagonal_exact_two_endpoint_shells
    C exponent hexp honeLoss t
  change retainedActiveViolationCoords C qS.1.1
      (netCollisionCertifiedDiagonal C exponent hexp honeLoss s) =
      {cfS} ∧
    retainedActiveViolationCoords C pS.1.2
      (netCollisionCertifiedDiagonal C exponent hexp honeLoss s) =
      {crS} at hS
  change retainedActiveViolationCoords C qT.1.1
      (netCollisionCertifiedDiagonal C exponent hexp honeLoss t) =
      {cfT} ∧
    retainedActiveViolationCoords C pT.1.2
      (netCollisionCertifiedDiagonal C exponent hexp honeLoss t) =
      {crT} at hT
  have hv : pS.1.2 = pT.1.2 := hupper
  have hsets : ({crS} : Finset (Fin n)) = {crT} := calc
    ({crS} : Finset (Fin n)) =
      retainedActiveViolationCoords C pS.1.2
        (netCollisionCertifiedDiagonal C exponent hexp honeLoss s) := hS.2.symm
    _ = retainedActiveViolationCoords C pT.1.2
        (netCollisionCertifiedDiagonal C exponent hexp honeLoss t) := by
      rw [hv, hdiag]
    _ = {crT} := hT.2
  have hm : crS ∈ ({crT} : Finset (Fin n)) := by
    rw [← hsets]
    simp
  exact Finset.mem_singleton.mp hm

/-- FOUR-bit same-diagonal reuse demands distinct original SOFT
bridge endpoints in BOTH roles; a shared lower OR a shared upper
bridge endpoint necessarily forces a common original flip colour,
contradicting the already-certified four-bit disjoint-colour law. -/
theorem net_collision_four_bit_same_diagonal_forces_both_bridge_endpoints_distinct
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
    (hfour :
      (Finset.univ.filter (fun e : Fin n => s.1 e ≠ t.1 e)).card = 4) :
    (netCollisionCertifiedBridgeOwner C exponent hexp honeLoss s).1 ≠
      (netCollisionCertifiedBridgeOwner C exponent hexp honeLoss t).1 ∧
    (netCollisionCertifiedBridgeOwner C exponent hexp honeLoss s).2 ≠
      (netCollisionCertifiedBridgeOwner C exponent hexp honeLoss t).2 := by
  classical
  have hdis :=
    (net_collision_equal_diagonal_four_bits_iff_disjoint_colours
      C exponent hexp honeLoss s t hdiag).mp hfour
  have hdis' := Finset.disjoint_left.mp hdis
  constructor
  · intro hl
    have hc := net_collision_equal_diagonal_same_lower_forward_colour_eq
      C exponent hexp honeLoss s t hdiag hl
    let cf := transportablePairColor C
      (transportableWordCarrier C
        (netCollisionCertifiedForwardSource C exponent hexp honeLoss s))
    have hmemS :
        cf ∈ netCollisionCanonicalColourSupport C exponent hexp honeLoss s := by
      simp [cf, netCollisionCanonicalColourSupport]
    have hmemT :
        cf ∈ netCollisionCanonicalColourSupport C exponent hexp honeLoss t := by
      simp [cf, netCollisionCanonicalColourSupport, hc]
    exact hdis' hmemS hmemT
  · intro hu
    have hc := net_collision_equal_diagonal_same_upper_reverse_colour_eq
      C exponent hexp honeLoss s t hdiag hu
    let cr := strictDescentRigidPairColor C exponent hexp honeLoss
      (strictDescentRigidWordCarrier C exponent
        (netCollisionCertifiedReverseSource C exponent hexp honeLoss s))
    have hmemS :
        cr ∈ netCollisionCanonicalColourSupport C exponent hexp honeLoss s := by
      simp [cr, netCollisionCanonicalColourSupport]
    have hmemT :
        cr ∈ netCollisionCanonicalColourSupport C exponent hexp honeLoss t := by
      simp [cr, netCollisionCanonicalColourSupport, hc]
    exact hdis' hmemS hmemT

#print axioms net_collision_equal_diagonal_same_lower_forward_colour_eq
#print axioms net_collision_equal_diagonal_same_upper_reverse_colour_eq
#print axioms net_collision_four_bit_same_diagonal_forces_both_bridge_endpoints_distinct

end OrderedEdgeColoring
end JSP000404Research
