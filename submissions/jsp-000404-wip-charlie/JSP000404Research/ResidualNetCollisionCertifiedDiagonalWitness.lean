import JSP000404Research.ResidualNetCollisionVariableDiagonalLedger
import Mathlib.Tactic

/-!
# Canonical actual NET-collision diagonal from uniquely determined hard transports

The preceding global three-way ledger accepted freely selected flip
colours. Here every genuine NET forward/reverse collision word w
has a certified forward hard source x and reverse strict-rigid hard
source y with common sink w. Both sources are UNIQUE because each
transport has already been proved globally injective.

We use these genuine sources, NOT hypothetical bridge candidates,
to select the forward/reverse flip colours of w. This constructs
a deterministic actual-collision diagonal without adding a
geometric selection or Hall hypothesis.
-/

namespace JSP000404Research
namespace OrderedEdgeColoring

/-- Every genuine NET collision admits ORIGINAL hard source witnesses
for both independent global injections. -/
theorem net_collision_has_unique_candidate_sources
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexp : ∀ v, exponent v ≤ n)
    (honeLoss : ∀ v, (active C v).card ≤ n - exponent v + 1)
    (w : {word : Fin n → Bool //
      word ∈ netActualForwardReverseCollisionWords
        C exponent hexp honeLoss}) :
    ∃ x : {word : Fin n → Bool //
        word ∈ transportableHardOverlapCompletionWords C},
      ∃ y : {word : Fin n → Bool //
          word ∈ netStrictDescentRigidWords C exponent},
        (transportableHardWordToSingletonOrSoft C x).1 = w.1 ∧
        (strictDescentRigidWordToSingletonOrSoft
          C exponent hexp honeLoss y).1 = w.1 := by
  classical
  have hactual :=
    net_actual_collision_subset_all_actual C exponent hexp honeLoss w.2
  have hF : w.1 ∈ forwardHardTransportSinkWords C :=
    (Finset.mem_inter.mp hactual).1
  have hR : w.1 ∈
      reverseStrictRigidSinkWords C exponent hexp honeLoss :=
    (Finset.mem_inter.mp hactual).2
  unfold forwardHardTransportSinkWords at hF
  unfold reverseStrictRigidSinkWords at hR
  obtain ⟨x, _, hx⟩ := Finset.mem_image.mp hF
  obtain ⟨y, _, hy⟩ := Finset.mem_image.mp hR
  exact ⟨x, y, hx, hy⟩

/-- The actual NET-collision forward hard source is uniquely
determined by the common sink word, not by a noncanonical choice. -/
theorem net_collision_forward_source_unique
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexp : ∀ v, exponent v ≤ n)
    (honeLoss : ∀ v, (active C v).card ≤ n - exponent v + 1)
    (w : {word : Fin n → Bool //
      word ∈ netActualForwardReverseCollisionWords
        C exponent hexp honeLoss})
    (x x' : {word : Fin n → Bool //
      word ∈ transportableHardOverlapCompletionWords C})
    (hx : (transportableHardWordToSingletonOrSoft C x).1 = w.1)
    (hx' : (transportableHardWordToSingletonOrSoft C x').1 = w.1) :
    x = x' := by
  apply transportableHardWordToSingletonOrSoft_injective C
  apply Subtype.ext
  exact hx.trans hx'.symm

/-- Likewise the reverse strict-rigid original hard source is
uniquely determined by the same collision sink. -/
theorem net_collision_reverse_source_unique
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexp : ∀ v, exponent v ≤ n)
    (honeLoss : ∀ v, (active C v).card ≤ n - exponent v + 1)
    (w : {word : Fin n → Bool //
      word ∈ netActualForwardReverseCollisionWords
        C exponent hexp honeLoss})
    (y y' : {word : Fin n → Bool //
      word ∈ netStrictDescentRigidWords C exponent})
    (hy : (strictDescentRigidWordToSingletonOrSoft
      C exponent hexp honeLoss y).1 = w.1)
    (hy' : (strictDescentRigidWordToSingletonOrSoft
      C exponent hexp honeLoss y').1 = w.1) :
    y = y' := by
  apply strictDescentRigidWordToSingletonOrSoft_injective
    C exponent hexp honeLoss
  apply Subtype.ext
  exact hy.trans hy'.symm

/-- The chosen forward source of an actual NET collision. Its
uniqueness is certified above; Classical.choose only realizes it. -/
noncomputable def netCollisionCertifiedForwardSource
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexp : ∀ v, exponent v ≤ n)
    (honeLoss : ∀ v, (active C v).card ≤ n - exponent v + 1)
    (w : {word : Fin n → Bool //
      word ∈ netActualForwardReverseCollisionWords
        C exponent hexp honeLoss}) :
    {word : Fin n → Bool //
      word ∈ transportableHardOverlapCompletionWords C} :=
  Classical.choose
    (net_collision_has_unique_candidate_sources
      C exponent hexp honeLoss w)

/-- The chosen reverse source of the SAME actual NET collision. -/
noncomputable def netCollisionCertifiedReverseSource
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexp : ∀ v, exponent v ≤ n)
    (honeLoss : ∀ v, (active C v).card ≤ n - exponent v + 1)
    (w : {word : Fin n → Bool //
      word ∈ netActualForwardReverseCollisionWords
        C exponent hexp honeLoss}) :
    {word : Fin n → Bool //
      word ∈ netStrictDescentRigidWords C exponent} :=
  Classical.choose
    (Classical.choose_spec
      (net_collision_has_unique_candidate_sources
        C exponent hexp honeLoss w))

/-- The selected forward and reverse sources REALLY transport
into the asserted NET collision sink word. -/
theorem net_collision_certified_sources_same_sink
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexp : ∀ v, exponent v ≤ n)
    (honeLoss : ∀ v, (active C v).card ≤ n - exponent v + 1)
    (w : {word : Fin n → Bool //
      word ∈ netActualForwardReverseCollisionWords
        C exponent hexp honeLoss}) :
    (transportableHardWordToSingletonOrSoft C
      (netCollisionCertifiedForwardSource C exponent hexp honeLoss w)).1 =
        w.1 ∧
    (strictDescentRigidWordToSingletonOrSoft
      C exponent hexp honeLoss
      (netCollisionCertifiedReverseSource C exponent hexp honeLoss w)).1 =
        w.1 := by
  exact Classical.choose_spec
    (Classical.choose_spec
      (net_collision_has_unique_candidate_sources
        C exponent hexp honeLoss w))

/-- Genuine source-dependent opposite diagonal for the unique
original forward/reverse hard carriers of each NET collision. -/
noncomputable def netCollisionCertifiedDiagonal
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexp : ∀ v, exponent v ≤ n)
    (honeLoss : ∀ v, (active C v).card ≤ n - exponent v + 1)
    (w : {word : Fin n → Bool //
      word ∈ netActualForwardReverseCollisionWords
        C exponent hexp honeLoss}) : Fin n → Bool :=
  let x := netCollisionCertifiedForwardSource C exponent hexp honeLoss w
  let y := netCollisionCertifiedReverseSource C exponent hexp honeLoss w
  let cf := transportablePairColor C (transportableWordCarrier C x)
  let cr := strictDescentRigidPairColor
    C exponent hexp honeLoss (strictDescentRigidWordCarrier C exponent y)
  flipCompletionWord cf (flipCompletionWord cr w.1)

#print axioms net_collision_has_unique_candidate_sources
#print axioms net_collision_forward_source_unique
#print axioms net_collision_reverse_source_unique
#print axioms net_collision_certified_sources_same_sink

end OrderedEdgeColoring
end JSP000404Research
