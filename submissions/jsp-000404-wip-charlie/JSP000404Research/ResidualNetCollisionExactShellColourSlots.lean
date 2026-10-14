import JSP000404Research.ResidualNetCollisionTargetBridgeColourSlots
import Mathlib.Tactic

/-!
# Target-exact original bridge endpoint colour slots

Earlier source-native lower/upper colour-slot bounds only required that
the original other flip colour was inactive at a selected endpoint AND
that this endpoint participated in some compatible candidate bridge.
Such coarse slots could include colours unrelated to the particular
diagonal target d.

The ACTUAL second flip colour is precisely the unique retained-active
bit violated by d at the OTHER bridge endpoint, by the previously
verified exact singleton shell law. Here we retain ONLY original
lower/upper vertex-and-colour slots witnessed by an eligible target
bridge whose other vertex actually has that exact violated bit.

Every genuine NET collision source maps injectively into either exact
slot pool. This refines both existing coarse slot bounds. The pools
still encode potential covered SOFT bridges, not true Boolean holes.
-/

namespace JSP000404Research
namespace OrderedEdgeColoring

/-- A lower endpoint b and reverse colour cr qualify for d only if
some source-compatible target-shell soft bridge (b,v) has cr as
one of the ACTUAL violated retained-active bits at v, while cr is
retained-INACTIVE at b. -/
noncomputable def targetLowerExactShellColourSlots
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (d : Fin n → Bool) : Finset (V × Fin n) := by
  classical
  exact Finset.univ.filter (fun p =>
    p.2 ∉ retainedActive C p.1 ∧
    ∃ v : V,
      (p.1, v) ∈ targetDoubleShellTwoBitBridgeCarriers C exponent d ∧
      p.2 ∈ retainedActiveViolationCoords C v d)

/-- Dual upper endpoint v and forward colour cf slots: cf must be
inactive at v and an ACTUAL target-shell violation at an eligible
original lower bridge endpoint b. -/
noncomputable def targetUpperExactShellColourSlots
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (d : Fin n → Bool) : Finset (V × Fin n) := by
  classical
  exact Finset.univ.filter (fun p =>
    p.2 ∉ retainedActive C p.1 ∧
    ∃ b : V,
      (b, p.1) ∈ targetDoubleShellTwoBitBridgeCarriers C exponent d ∧
      p.2 ∈ retainedActiveViolationCoords C b d)

/-- Target-exact slots are a genuine, possibly proper, subset of
the previous lower endpoint-inactive-colour slots. -/
theorem target_lower_exact_shell_slots_subset_coarse
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ) (d : Fin n → Bool) :
    targetLowerExactShellColourSlots C exponent d ⊆
      targetLowerDoubleShellInactiveColourSlots C exponent d := by
  classical
  intro p hp
  obtain ⟨_, ⟨hi, v, hv, _⟩⟩ := Finset.mem_filter.mp hp
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, ⟨v, hv⟩, hi⟩

/-- Same refinement for the forward-upper endpoint slots. -/
theorem target_upper_exact_shell_slots_subset_coarse
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ) (d : Fin n → Bool) :
    targetUpperExactShellColourSlots C exponent d ⊆
      targetUpperDoubleShellInactiveColourSlots C exponent d := by
  classical
  intro p hp
  obtain ⟨_, ⟨hi, b, hb, _⟩⟩ := Finset.mem_filter.mp hp
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, ⟨b, hb⟩, hi⟩

/-- Each genuine source s with canonical target d determines a
target-exact LOWER endpoint/reverse-colour slot. -/
theorem net_collision_actual_lower_exact_slot_mem
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexp : ∀ v, exponent v ≤ n)
    (honeLoss : ∀ v, (active C v).card ≤ n - exponent v + 1)
    (s : {w : Fin n → Bool //
      w ∈ netActualForwardReverseCollisionWords C exponent hexp honeLoss}) :
    ((netCollisionCertifiedBridgeOwner C exponent hexp honeLoss s).1,
      strictDescentRigidPairColor C exponent hexp honeLoss
        (strictDescentRigidWordCarrier C exponent
          (netCollisionCertifiedReverseSource C exponent hexp honeLoss s))) ∈
      targetLowerExactShellColourSlots C exponent
        (netCollisionCertifiedDiagonal C exponent hexp honeLoss s) := by
  classical
  let q := strictDescentRigidWordCarrier C exponent
    (netCollisionCertifiedReverseSource C exponent hexp honeLoss s)
  let p := transportableWordCarrier C
    (netCollisionCertifiedForwardSource C exponent hexp honeLoss s)
  let cr := strictDescentRigidPairColor C exponent hexp honeLoss q
  let cf := transportablePairColor C p
  let d := netCollisionCertifiedDiagonal C exponent hexp honeLoss s
  have hb : (netCollisionCertifiedBridgeOwner C exponent hexp honeLoss s) =
      (q.1.1, p.1.2) := rfl
  have hnot : cr ∉ retainedActive C q.1.1 :=
    (strictDescentRigidPairColor_spec C exponent hexp honeLoss q).2
  have hbridge := net_collision_bridge_owner_mem_target_double_shell
    C exponent hexp honeLoss s
  change (q.1.1, p.1.2) ∈
    targetDoubleShellTwoBitBridgeCarriers C exponent d at hbridge
  have hshell := net_collision_certified_diagonal_exact_two_endpoint_shells
    C exponent hexp honeLoss s
  change retainedActiveViolationCoords C q.1.1 d = {cf} ∧
    retainedActiveViolationCoords C p.1.2 d = {cr} at hshell
  have hcr : cr ∈ retainedActiveViolationCoords C p.1.2 d := by
    rw [hshell.2]
    simp
  change (q.1.1, cr) ∈ targetLowerExactShellColourSlots C exponent d
  exact Finset.mem_filter.mpr
    ⟨Finset.mem_univ _, hnot, ⟨p.1.2, hbridge, hcr⟩⟩

/-- Dual genuine source assignment to its target-exact UPPER
endpoint / forward-colour slot. -/
theorem net_collision_actual_upper_exact_slot_mem
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexp : ∀ v, exponent v ≤ n)
    (honeLoss : ∀ v, (active C v).card ≤ n - exponent v + 1)
    (s : {w : Fin n → Bool //
      w ∈ netActualForwardReverseCollisionWords C exponent hexp honeLoss}) :
    ((netCollisionCertifiedBridgeOwner C exponent hexp honeLoss s).2,
      transportablePairColor C
        (transportableWordCarrier C
          (netCollisionCertifiedForwardSource C exponent hexp honeLoss s))) ∈
      targetUpperExactShellColourSlots C exponent
        (netCollisionCertifiedDiagonal C exponent hexp honeLoss s) := by
  classical
  let q := strictDescentRigidWordCarrier C exponent
    (netCollisionCertifiedReverseSource C exponent hexp honeLoss s)
  let p := transportableWordCarrier C
    (netCollisionCertifiedForwardSource C exponent hexp honeLoss s)
  let cr := strictDescentRigidPairColor C exponent hexp honeLoss q
  let cf := transportablePairColor C p
  let d := netCollisionCertifiedDiagonal C exponent hexp honeLoss s
  have hnot : cf ∉ retainedActive C p.1.2 :=
    (transportablePairColor_spec C p).2
  have hbridge := net_collision_bridge_owner_mem_target_double_shell
    C exponent hexp honeLoss s
  change (q.1.1, p.1.2) ∈
    targetDoubleShellTwoBitBridgeCarriers C exponent d at hbridge
  have hshell := net_collision_certified_diagonal_exact_two_endpoint_shells
    C exponent hexp honeLoss s
  change retainedActiveViolationCoords C q.1.1 d = {cf} ∧
    retainedActiveViolationCoords C p.1.2 d = {cr} at hshell
  have hcf : cf ∈ retainedActiveViolationCoords C q.1.1 d := by
    rw [hshell.1]
    simp
  change (p.1.2, cf) ∈ targetUpperExactShellColourSlots C exponent d
  exact Finset.mem_filter.mpr
    ⟨Finset.mem_univ _, hnot, ⟨q.1.1, hbridge, hcf⟩⟩

/-- The previously proven lower endpoint/reverse-colour map is
injective on a fixed-target source fibre. Here all of its image
is in the strictly filtered target-exact shell-slot pool. -/
theorem net_collision_target_fibre_card_le_lower_exact_shell_slots
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexp : ∀ v, exponent v ≤ n)
    (honeLoss : ∀ v, (active C v).card ≤ n - exponent v + 1)
    (d : Fin n → Bool) :
    (netCollisionCertifiedDiagonalFibre C exponent hexp honeLoss d).card ≤
      (targetLowerExactShellColourSlots C exponent d).card := by
  classical
  let S := {w : Fin n → Bool //
    w ∈ netActualForwardReverseCollisionWords C exponent hexp honeLoss}
  let F : Finset S :=
    netCollisionCertifiedDiagonalFibre C exponent hexp honeLoss d
  let f : {s : S // s ∈ F} → V × Fin n :=
    fun s => ((netCollisionCertifiedBridgeOwner C exponent hexp honeLoss s.1).1,
      strictDescentRigidPairColor C exponent hexp honeLoss
        (strictDescentRigidWordCarrier C exponent
          (netCollisionCertifiedReverseSource C exponent hexp honeLoss s.1)))
  have hinj : Function.Injective f := by
    intro s t heq
    have hb := congrArg (fun p : V × Fin n => p.1) heq
    have hcr := congrArg (fun p : V × Fin n => p.2) heq
    change strictDescentRigidPairColor C exponent hexp honeLoss
      (strictDescentRigidWordCarrier C exponent
        (netCollisionCertifiedReverseSource C exponent hexp honeLoss s.1)) =
      strictDescentRigidPairColor C exponent hexp honeLoss
      (strictDescentRigidWordCarrier C exponent
        (netCollisionCertifiedReverseSource C exponent hexp honeLoss t.1))
      at hcr
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
        targetLowerExactShellColourSlots C exponent d := by
    intro p hp
    obtain ⟨s, _, rfl⟩ := Finset.mem_image.mp hp
    have hs := net_collision_actual_lower_exact_slot_mem
      C exponent hexp honeLoss s.1
    have hd : netCollisionCertifiedDiagonal C exponent hexp honeLoss s.1 = d :=
      (Finset.mem_filter.mp s.2).2
    simpa only [hd] using hs
  change F.card ≤ (targetLowerExactShellColourSlots C exponent d).card
  calc
    F.card = (Finset.univ : Finset {s : S // s ∈ F}).card := by simp
    _ = ((Finset.univ : Finset {s : S // s ∈ F}).image f).card :=
      (Finset.card_image_of_injective _ hinj).symm
    _ ≤ _ := Finset.card_le_card hsub

/-- Same target-exact slot-capacity refinement on the upper side. -/
theorem net_collision_target_fibre_card_le_upper_exact_shell_slots
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexp : ∀ v, exponent v ≤ n)
    (honeLoss : ∀ v, (active C v).card ≤ n - exponent v + 1)
    (d : Fin n → Bool) :
    (netCollisionCertifiedDiagonalFibre C exponent hexp honeLoss d).card ≤
      (targetUpperExactShellColourSlots C exponent d).card := by
  classical
  let S := {w : Fin n → Bool //
    w ∈ netActualForwardReverseCollisionWords C exponent hexp honeLoss}
  let F : Finset S :=
    netCollisionCertifiedDiagonalFibre C exponent hexp honeLoss d
  let f : {s : S // s ∈ F} → V × Fin n :=
    fun s => ((netCollisionCertifiedBridgeOwner C exponent hexp honeLoss s.1).2,
      transportablePairColor C
        (transportableWordCarrier C
          (netCollisionCertifiedForwardSource C exponent hexp honeLoss s.1)))
  have hinj : Function.Injective f := by
    intro s t heq
    have hv := congrArg (fun p : V × Fin n => p.1) heq
    have hcf := congrArg (fun p : V × Fin n => p.2) heq
    change transportablePairColor C
      (transportableWordCarrier C
        (netCollisionCertifiedForwardSource C exponent hexp honeLoss s.1)) =
      transportablePairColor C
      (transportableWordCarrier C
        (netCollisionCertifiedForwardSource C exponent hexp honeLoss t.1))
      at hcf
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
        targetUpperExactShellColourSlots C exponent d := by
    intro p hp
    obtain ⟨s, _, rfl⟩ := Finset.mem_image.mp hp
    have hs := net_collision_actual_upper_exact_slot_mem
      C exponent hexp honeLoss s.1
    have hd : netCollisionCertifiedDiagonal C exponent hexp honeLoss s.1 = d :=
      (Finset.mem_filter.mp s.2).2
    simpa only [hd] using hs
  change F.card ≤ (targetUpperExactShellColourSlots C exponent d).card
  calc
    F.card = (Finset.univ : Finset {s : S // s ∈ F}).card := by simp
    _ = ((Finset.univ : Finset {s : S // s ∈ F}).image f).card :=
      (Finset.card_image_of_injective _ hinj).symm
    _ ≤ _ := Finset.card_le_card hsub

#print axioms target_lower_exact_shell_slots_subset_coarse
#print axioms target_upper_exact_shell_slots_subset_coarse
#print axioms net_collision_actual_lower_exact_slot_mem
#print axioms net_collision_actual_upper_exact_slot_mem
#print axioms net_collision_target_fibre_card_le_lower_exact_shell_slots
#print axioms net_collision_target_fibre_card_le_upper_exact_shell_slots

end OrderedEdgeColoring
end JSP000404Research
