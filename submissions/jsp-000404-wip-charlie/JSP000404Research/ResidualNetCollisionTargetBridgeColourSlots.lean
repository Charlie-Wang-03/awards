import JSP000404Research.ResidualNetCollisionFixedEndpointColourInjection
import Mathlib.Tactic

/-!
# Non-repeating original flip-colour slots over TARGET-COMPATIBLE soft bridges

The prior fixed-endpoint source-star injections give linear upper bounds
by the retained-INACTIVE colour count at each centre. We now aggregate
them without multiplying by the number of SOFT bridge neighbours.

For a particular actual canonical diagonal target d, only lower
(respectively upper) vertices that occur as an endpoint of a
target-compatible double-shell candidate bridge are allowed. To each
genuine NET collision source s, attach the pair consisting of its
original lower endpoint b_s and its original REVERSE hard flip cr_s
(or dually upper endpoint v_s and original FORWARD flip cf_s).
These are injective labels AT FIXED d, and the colour is inactive
at that endpoint.

Hence its actual target fibre embeds into a fully explicit finite
set of endpoint-inactive-colour slots, as an alternative to the
target-compatible BRIDGE-count bound. Multiple candidate bridges
with the same endpoint and same other-colour CANNOT reuse that slot.

No hole payment or unreserved profile credit is asserted.
-/

namespace JSP000404Research
namespace OrderedEdgeColoring

/-- The permitted lower-endpoint / inactive reverse-flip slots for
a fixed target d. Every eligible lower vertex must appear in some
source-compatible *candidate* double-shell soft bridge for d. -/
noncomputable def targetLowerDoubleShellInactiveColourSlots
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (d : Fin n → Bool) : Finset (V × Fin n) := by
  classical
  exact Finset.univ.filter (fun p =>
    (∃ v : V,
      (p.1,v) ∈ targetDoubleShellTwoBitBridgeCarriers C exponent d) ∧
    p.2 ∉ retainedActive C p.1)

/-- Dual target-specific upper-endpoint / inactive forward-flip slots. -/
noncomputable def targetUpperDoubleShellInactiveColourSlots
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (d : Fin n → Bool) : Finset (V × Fin n) := by
  classical
  exact Finset.univ.filter (fun p =>
    (∃ b : V,
      (b,p.1) ∈ targetDoubleShellTwoBitBridgeCarriers C exponent d) ∧
    p.2 ∉ retainedActive C p.1)

/-- The actual same-diagonal source fibre injects into original
lower-vertex / reverse-inactive-colour slots. This DOES NOT multiply
the per-vertex inactive dimension by its number of candidate bridges. -/
theorem net_collision_diagonal_fibre_card_le_lower_target_colour_slots
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexp : ∀ v, exponent v ≤ n)
    (honeLoss : ∀ v, (active C v).card ≤ n - exponent v + 1)
    (d : Fin n → Bool) :
    (netCollisionCertifiedDiagonalFibre C exponent hexp honeLoss d).card ≤
      (targetLowerDoubleShellInactiveColourSlots C exponent d).card := by
  classical
  let S := {w : Fin n → Bool //
    w ∈ netActualForwardReverseCollisionWords C exponent hexp honeLoss}
  let F : Finset S :=
    netCollisionCertifiedDiagonalFibre C exponent hexp honeLoss d
  let f : {s : S // s ∈ F} → V × Fin n :=
    fun s => ((netCollisionCertifiedBridgeOwner
      C exponent hexp honeLoss s.1).1,
      strictDescentRigidPairColor C exponent hexp honeLoss
        (strictDescentRigidWordCarrier C exponent
          (netCollisionCertifiedReverseSource C exponent hexp honeLoss s.1)))
  have hinj : Function.Injective f := by
    intro s t heq
    have hb : (netCollisionCertifiedBridgeOwner
        C exponent hexp honeLoss s.1).1 =
      (netCollisionCertifiedBridgeOwner C exponent hexp honeLoss t.1).1 :=
      congrArg (fun p : V × Fin n => p.1) heq
    have hcr : strictDescentRigidPairColor C exponent hexp honeLoss
        (strictDescentRigidWordCarrier C exponent
          (netCollisionCertifiedReverseSource C exponent hexp honeLoss s.1)) =
      strictDescentRigidPairColor C exponent hexp honeLoss
        (strictDescentRigidWordCarrier C exponent
          (netCollisionCertifiedReverseSource C exponent hexp honeLoss t.1)) :=
      congrArg (fun p : V × Fin n => p.2) heq
    have hs : netCollisionCertifiedDiagonal C exponent hexp honeLoss s.1 = d :=
      (Finset.mem_filter.mp s.2).2
    have ht : netCollisionCertifiedDiagonal C exponent hexp honeLoss t.1 = d :=
      (Finset.mem_filter.mp t.2).2
    have hcf := net_collision_equal_diagonal_same_lower_forward_colour_eq
      C exponent hexp honeLoss s.1 t.1 (hs.trans ht.symm) hb
    have hsupport :
      netCollisionCanonicalColourSupport C exponent hexp honeLoss s.1 =
      netCollisionCanonicalColourSupport C exponent hexp honeLoss t.1 := by
      unfold netCollisionCanonicalColourSupport
      rw [hcf, hcr]
    have heqsource := net_collision_canonical_support_fibre_injective
      C exponent hexp honeLoss s.1 t.1 (hs.trans ht.symm) hsupport
    exact Subtype.ext heqsource
  have hsub :
      (Finset.univ : Finset {s : S // s ∈ F}).image f ⊆
        targetLowerDoubleShellInactiveColourSlots C exponent d := by
    intro p hp
    obtain ⟨s, _, rfl⟩ := Finset.mem_image.mp hp
    have hd : netCollisionCertifiedDiagonal C exponent hexp honeLoss s.1 = d :=
      (Finset.mem_filter.mp s.2).2
    have hb := net_collision_bridge_owner_mem_target_double_shell
      C exponent hexp honeLoss s.1
    rw [hd] at hb
    let q := strictDescentRigidWordCarrier C exponent
      (netCollisionCertifiedReverseSource C exponent hexp honeLoss s.1)
    have hnot : strictDescentRigidPairColor C exponent hexp honeLoss q ∉
      retainedActive C q.1.1 :=
      (strictDescentRigidPairColor_spec C exponent hexp honeLoss q).2
    have hendpoint : (netCollisionCertifiedBridgeOwner
        C exponent hexp honeLoss s.1).1 = q.1.1 := rfl
    change ((netCollisionCertifiedBridgeOwner C exponent hexp honeLoss s.1).1,
      strictDescentRigidPairColor C exponent hexp honeLoss q) ∈
        targetLowerDoubleShellInactiveColourSlots C exponent d
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_, ?_⟩
    · exact ⟨(netCollisionCertifiedBridgeOwner
        C exponent hexp honeLoss s.1).2, hb⟩
    · simpa only [hendpoint] using hnot
  change F.card ≤
    (targetLowerDoubleShellInactiveColourSlots C exponent d).card
  calc
    F.card = (Finset.univ : Finset {s : S // s ∈ F}).card := by simp
    _ = ((Finset.univ : Finset {s : S // s ∈ F}).image f).card :=
      (Finset.card_image_of_injective _ hinj).symm
    _ ≤ _ := Finset.card_le_card hsub

/-- Dual global fixed-target bound: actual NET sources inject into
upper-vertex / original forward-inactive-colour slots. -/
theorem net_collision_diagonal_fibre_card_le_upper_target_colour_slots
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexp : ∀ v, exponent v ≤ n)
    (honeLoss : ∀ v, (active C v).card ≤ n - exponent v + 1)
    (d : Fin n → Bool) :
    (netCollisionCertifiedDiagonalFibre C exponent hexp honeLoss d).card ≤
      (targetUpperDoubleShellInactiveColourSlots C exponent d).card := by
  classical
  let S := {w : Fin n → Bool //
    w ∈ netActualForwardReverseCollisionWords C exponent hexp honeLoss}
  let F : Finset S :=
    netCollisionCertifiedDiagonalFibre C exponent hexp honeLoss d
  let f : {s : S // s ∈ F} → V × Fin n :=
    fun s => ((netCollisionCertifiedBridgeOwner
      C exponent hexp honeLoss s.1).2,
      transportablePairColor C
        (transportableWordCarrier C
          (netCollisionCertifiedForwardSource C exponent hexp honeLoss s.1)))
  have hinj : Function.Injective f := by
    intro s t heq
    have hv : (netCollisionCertifiedBridgeOwner
        C exponent hexp honeLoss s.1).2 =
      (netCollisionCertifiedBridgeOwner C exponent hexp honeLoss t.1).2 :=
      congrArg (fun p : V × Fin n => p.1) heq
    have hcf : transportablePairColor C
        (transportableWordCarrier C
          (netCollisionCertifiedForwardSource C exponent hexp honeLoss s.1)) =
      transportablePairColor C
        (transportableWordCarrier C
          (netCollisionCertifiedForwardSource C exponent hexp honeLoss t.1)) :=
      congrArg (fun p : V × Fin n => p.2) heq
    have hs : netCollisionCertifiedDiagonal C exponent hexp honeLoss s.1 = d :=
      (Finset.mem_filter.mp s.2).2
    have ht : netCollisionCertifiedDiagonal C exponent hexp honeLoss t.1 = d :=
      (Finset.mem_filter.mp t.2).2
    have hcr := net_collision_equal_diagonal_same_upper_reverse_colour_eq
      C exponent hexp honeLoss s.1 t.1 (hs.trans ht.symm) hv
    have hsupport :
      netCollisionCanonicalColourSupport C exponent hexp honeLoss s.1 =
      netCollisionCanonicalColourSupport C exponent hexp honeLoss t.1 := by
      unfold netCollisionCanonicalColourSupport
      rw [hcf, hcr]
    have heqsource := net_collision_canonical_support_fibre_injective
      C exponent hexp honeLoss s.1 t.1 (hs.trans ht.symm) hsupport
    exact Subtype.ext heqsource
  have hsub :
      (Finset.univ : Finset {s : S // s ∈ F}).image f ⊆
        targetUpperDoubleShellInactiveColourSlots C exponent d := by
    intro p hp
    obtain ⟨s, _, rfl⟩ := Finset.mem_image.mp hp
    have hd : netCollisionCertifiedDiagonal C exponent hexp honeLoss s.1 = d :=
      (Finset.mem_filter.mp s.2).2
    have hb := net_collision_bridge_owner_mem_target_double_shell
      C exponent hexp honeLoss s.1
    rw [hd] at hb
    let q := transportableWordCarrier C
      (netCollisionCertifiedForwardSource C exponent hexp honeLoss s.1)
    have hnot : transportablePairColor C q ∉ retainedActive C q.1.2 :=
      (transportablePairColor_spec C q).2
    have hendpoint : (netCollisionCertifiedBridgeOwner
        C exponent hexp honeLoss s.1).2 = q.1.2 := rfl
    change ((netCollisionCertifiedBridgeOwner C exponent hexp honeLoss s.1).2,
      transportablePairColor C q) ∈
        targetUpperDoubleShellInactiveColourSlots C exponent d
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_, ?_⟩
    · exact ⟨(netCollisionCertifiedBridgeOwner
        C exponent hexp honeLoss s.1).1, hb⟩
    · simpa only [hendpoint] using hnot
  change F.card ≤
    (targetUpperDoubleShellInactiveColourSlots C exponent d).card
  calc
    F.card = (Finset.univ : Finset {s : S // s ∈ F}).card := by simp
    _ = ((Finset.univ : Finset {s : S // s ∈ F}).image f).card :=
      (Finset.card_image_of_injective _ hinj).symm
    _ ≤ _ := Finset.card_le_card hsub

/-- Exact global source-fibre duplicate debt is bounded by the sum
of positive LOWER target-specific inactive-colour-slot EXCESS.
No source-specific target is reused as a true Boolean hole. -/
theorem net_collision_duplicate_debt_le_sum_lower_colour_slot_excess
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexp : ∀ v, exponent v ≤ n)
    (honeLoss : ∀ v, (active C v).card ≤ n - exponent v + 1) :
    netCollisionCertifiedDuplicateDebt C exponent hexp honeLoss ≤
      ∑ d ∈ netCollisionCertifiedDiagonalWords C exponent hexp honeLoss,
        ((targetLowerDoubleShellInactiveColourSlots C exponent d).card - 1) := by
  rw [net_collision_certified_duplicate_debt_eq_sum_fibre_excess
    C exponent hexp honeLoss]
  apply Finset.sum_le_sum
  intro d hd
  have h := net_collision_diagonal_fibre_card_le_lower_target_colour_slots
    C exponent hexp honeLoss d
  omega

#print axioms net_collision_diagonal_fibre_card_le_lower_target_colour_slots
#print axioms net_collision_diagonal_fibre_card_le_upper_target_colour_slots
#print axioms net_collision_duplicate_debt_le_sum_lower_colour_slot_excess

end OrderedEdgeColoring
end JSP000404Research
