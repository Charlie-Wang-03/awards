import JSP000404Research.ResidualNetCollisionSameBridgeDiagonalInjection
import Mathlib.Tactic

/-!
# Source-native global bridge capacity for each canonical diagonal fibre

A GENUINE NET hard-source intersection selects a unique reverse-lower/
forward-upper bridge owner, which belongs to the doubly filtered
SOFT potential bridge carrier set: incomparable retained-active palettes
AND at least two retained-bit differences. This inclusion is proved
from actual original sources, not an assumed geometric Hall matching.

The newly verified fixed-BRIDGE diagonal injection then embeds
every fixed opposite-diagonal source fibre INTO the genuine potential
bridge carrier set. This yields a potentially much tighter per-target
multiplicity cap than the coordinate-only Nat.choose n 2 cap.

Neither bound identifies a covered diagonal as a true hole.
-/

namespace JSP000404Research
namespace OrderedEdgeColoring

/-- The owner of every actual NET collision is a genuine soft bridge,
satisfies source-certified incomparability, and has at least two
retained-bit discrepancies between its two endpoints. -/
theorem net_collision_certified_bridge_owner_mem_two_bit_carriers
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexp : ∀ v, exponent v ≤ n)
    (honeLoss : ∀ v, (active C v).card ≤ n - exponent v + 1)
    (s : {w : Fin n → Bool //
      w ∈ netActualForwardReverseCollisionWords
        C exponent hexp honeLoss}) :
    netCollisionCertifiedBridgeOwner C exponent hexp honeLoss s ∈
      twoBitDisagreementBridgeCarriers C exponent := by
  classical
  let x := netCollisionCertifiedForwardSource C exponent hexp honeLoss s
  let y := netCollisionCertifiedReverseSource C exponent hexp honeLoss s
  let p := transportableWordCarrier C x
  let q := strictDescentRigidWordCarrier C exponent y
  have hsrc := net_collision_certified_sources_same_sink
    C exponent hexp honeLoss s
  have hcoll : (transportableHardWordToSingletonOrSoft C x).1 =
    (strictDescentRigidWordToSingletonOrSoft
      C exponent hexp honeLoss y).1 := hsrc.1.trans hsrc.2.symm
  have howner :=
    forward_reverse_sink_collision_has_bridge_soft_owner
      C exponent hexp honeLoss x y hcoll
  change (q.1.1, p.1.2) ∈ softOverlapCarrierPairs C ∧
    (transportableHardWordToSingletonOrSoft C x).1 ∈
      carrierOverlapWords C (q.1.1, p.1.2) at howner
  have hp : p.1 ∈ transportableHardOverlapCarrierPairs C := p.2
  have hq : q.1 ∈ netStrictDescentRigidCarriers C exponent := q.2
  have hcandidate :
      (q.1.1, p.1.2) ∈ forwardReverseBridgeSoftCarriers C exponent := by
    change (q.1.1, p.1.2) ∈
      (softOverlapCarrierPairs C).filter _
    exact Finset.mem_filter.mpr
      ⟨howner.1, ⟨p.1, hp, q.1, hq, rfl, rfl⟩⟩
  have hpalette :=
    forward_reverse_collision_bridge_active_incomparable
      C exponent hexp honeLoss x y hcoll
  change ¬ retainedActive C q.1.1 ⊆ retainedActive C p.1.2 ∧
    ¬ retainedActive C p.1.2 ⊆ retainedActive C q.1.1 at hpalette
  have hbits :=
    forward_reverse_actual_collision_bridge_hamming_ge_two
      C exponent hexp honeLoss x y hcoll
  change 2 ≤ (retainedBitDisagreementCoords C q.1.1 p.1.2).card at hbits
  change (q.1.1, p.1.2) ∈ twoBitDisagreementBridgeCarriers C exponent
  exact Finset.mem_filter.mpr
    ⟨Finset.mem_filter.mpr ⟨hcandidate, hpalette⟩, hbits⟩

/-- The pair (ACTUAL opposite diagonal, ORIGINAL actual soft bridge)
is globally injective across ALL genuine NET sink collisions. -/
theorem net_collision_diagonal_bridge_pair_injective
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexp : ∀ v, exponent v ≤ n)
    (honeLoss : ∀ v, (active C v).card ≤ n - exponent v + 1) :
    Function.Injective
      (fun s : {w : Fin n → Bool //
        w ∈ netActualForwardReverseCollisionWords
          C exponent hexp honeLoss} =>
        (netCollisionCertifiedDiagonal C exponent hexp honeLoss s,
         netCollisionCertifiedBridgeOwner C exponent hexp honeLoss s)) := by
  intro s t heq
  exact net_collision_same_bridge_same_diagonal_source_eq
    C exponent hexp honeLoss s t
    (congrArg (fun v : (Fin n → Bool) × (V × V) => v.1) heq)
    (congrArg (fun v : (Fin n → Bool) × (V × V) => v.2) heq)

/-- For EVERY actual canonical target d, each original soft bridge
contributes at most ONE source. Hence the entire fixed target fibre
cannot exceed the number of genuine doubly filtered bridge carriers
(forward/reverse originals, incomparable active palettes, >=2 bits).
This does not charge any target to a true hole. -/
theorem net_collision_fixed_diagonal_fibre_card_le_two_bit_bridges
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexp : ∀ v, exponent v ≤ n)
    (honeLoss : ∀ v, (active C v).card ≤ n - exponent v + 1)
    (d : Fin n → Bool) :
    (netCollisionCertifiedDiagonalFibre
      C exponent hexp honeLoss d).card ≤
      (twoBitDisagreementBridgeCarriers C exponent).card := by
  classical
  let S := {w : Fin n → Bool //
    w ∈ netActualForwardReverseCollisionWords
      C exponent hexp honeLoss}
  let F : Finset S :=
    netCollisionCertifiedDiagonalFibre C exponent hexp honeLoss d
  let P := twoBitDisagreementBridgeCarriers C exponent
  let f : {s : S // s ∈ F} → V × V :=
    fun s => netCollisionCertifiedBridgeOwner
      C exponent hexp honeLoss s.1
  have hinj : Function.Injective f := by
    intro x y h
    apply Subtype.ext
    have hx : netCollisionCertifiedDiagonal
        C exponent hexp honeLoss x.1 = d :=
      (Finset.mem_filter.mp x.2).2
    have hy : netCollisionCertifiedDiagonal
        C exponent hexp honeLoss y.1 = d :=
      (Finset.mem_filter.mp y.2).2
    exact net_collision_same_bridge_same_diagonal_source_eq
      C exponent hexp honeLoss x.1 y.1
      (hx.trans hy.symm) h
  have hsubset : (Finset.univ : Finset {s : S // s ∈ F}).image f ⊆ P := by
    intro bridge h
    obtain ⟨s, _, rfl⟩ := Finset.mem_image.mp h
    exact net_collision_certified_bridge_owner_mem_two_bit_carriers
      C exponent hexp honeLoss s.1
  change F.card ≤ P.card
  calc
    F.card = (Finset.univ : Finset {s : S // s ∈ F}).card := by simp
    _ = ((Finset.univ : Finset {s : S // s ∈ F}).image f).card :=
      (Finset.card_image_of_injective _ hinj).symm
    _ ≤ P.card := Finset.card_le_card hsubset


/-- Genuine NET collisions admit a GLOBAL source count controlled by
the number of DISTINCT canonical diagonal targets times the number
of authentic source-compatible doubly filtered soft bridges. This is
a genuine geometric-combinatorial refinement of the colour-only
choose-two bound (the better bound depends on the actual bridge pool). -/
theorem net_collision_card_le_distinct_diagonals_times_two_bit_bridges
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexp : ∀ v, exponent v ≤ n)
    (honeLoss : ∀ v, (active C v).card ≤ n - exponent v + 1) :
    (netActualForwardReverseCollisionWords C exponent hexp honeLoss).card ≤
      (netCollisionCertifiedDiagonalWords C exponent hexp honeLoss).card *
      (twoBitDisagreementBridgeCarriers C exponent).card := by
  classical
  let I := netActualForwardReverseCollisionWords C exponent hexp honeLoss
  let Src := {w : Fin n → Bool // w ∈ I}
  let D := netCollisionCertifiedDiagonalWords C exponent hexp honeLoss
  let B := twoBitDisagreementBridgeCarriers C exponent
  let f : Src → (Fin n → Bool) × (V × V) :=
    fun s => (netCollisionCertifiedDiagonal C exponent hexp honeLoss s,
      netCollisionCertifiedBridgeOwner C exponent hexp honeLoss s)
  have hinj : Function.Injective f :=
    net_collision_diagonal_bridge_pair_injective C exponent hexp honeLoss
  have hsubset : (Finset.univ : Finset Src).image f ⊆ D.product B := by
    intro pair hp
    obtain ⟨s, _, rfl⟩ := Finset.mem_image.mp hp
    apply Finset.mem_product.mpr
    constructor
    · unfold D netCollisionCertifiedDiagonalWords
      exact Finset.mem_image.mpr ⟨s, Finset.mem_univ _, rfl⟩
    · exact net_collision_certified_bridge_owner_mem_two_bit_carriers
        C exponent hexp honeLoss s
  change I.card ≤ D.card * B.card
  calc
    I.card = (Finset.univ : Finset Src).card := by simp [Src]
    _ = ((Finset.univ : Finset Src).image f).card :=
      (Finset.card_image_of_injective _ hinj).symm
    _ ≤ (D.product B).card := Finset.card_le_card hsubset
    _ = D.card * B.card := Finset.card_product D B

/-- A precise, optional sufficient criterion for ZERO actual
canonical duplicate-image debt: if there is at most ONE genuine
two-bit incomparable soft bridge carrier, no pair of different
actual sources can hit the same diagonal. We do NOT assert the
planar AngleCap hypotheses imply this one-bridge condition. -/
theorem net_collision_duplicate_debt_zero_of_at_most_one_two_bit_bridge
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexp : ∀ v, exponent v ≤ n)
    (honeLoss : ∀ v, (active C v).card ≤ n - exponent v + 1)
    (hone : (twoBitDisagreementBridgeCarriers C exponent).card ≤ 1) :
    netCollisionCertifiedDuplicateDebt C exponent hexp honeLoss = 0 := by
  have hmass :=
    net_collision_card_le_distinct_diagonals_times_two_bit_bridges
      C exponent hexp honeLoss
  have hle :
      (netActualForwardReverseCollisionWords C exponent hexp honeLoss).card ≤
      (netCollisionCertifiedDiagonalWords C exponent hexp honeLoss).card := by
    by_cases hz :
        (twoBitDisagreementBridgeCarriers C exponent).card = 0
    · simp only [hz, Nat.mul_zero] at hmass
      omega
    · have honeq :
          (twoBitDisagreementBridgeCarriers C exponent).card = 1 := by
        omega
      simpa [honeq] using hmass
  exact Nat.sub_eq_zero_iff_le.mpr hle

#print axioms net_collision_card_le_distinct_diagonals_times_two_bit_bridges
#print axioms net_collision_duplicate_debt_zero_of_at_most_one_two_bit_bridge

#print axioms net_collision_certified_bridge_owner_mem_two_bit_carriers
#print axioms net_collision_diagonal_bridge_pair_injective
#print axioms net_collision_fixed_diagonal_fibre_card_le_two_bit_bridges

end OrderedEdgeColoring
end JSP000404Research
