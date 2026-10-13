import JSP000404Research.ResidualNetCollisionSharedVertexInactiveCapacity
import Mathlib.Tactic

/-!
# Actual NET same-target source multiplicity, per ORIGINAL bridge endpoint

For any fixed canonical target d and any fixed original reverse-LOWER
bridge vertex b, every genuine NET source s in the fibre with that b
has a unique original forward flip colour dictated by the singleton
target-bit violation at b. Therefore its original REVERSE flip colour,
which is INACTIVE at b, uniquely tags its source. Conversely for a
fixed forward-UPPER vertex v, original FORWARD flip colour, inactive at
v, uniquely tags the source.

The resulting exact endpoint-star fibre capacities depend LINEARLY on
the number of inactive colours at that centre, not exponentially on
its completion cube size or on global choose(n,2). They also imply
the star at an endpoint with at most one inactive bit is injective
for any target. No new axioms, sorry, global hole payment or planar
AngleCap assumptions.
-/

namespace JSP000404Research
namespace OrderedEdgeColoring

/-- Genuine collision sources hitting target d whose original soft
bridge has reverse-LOWER endpoint b. -/
noncomputable def netCollisionLowerVertexDiagonalFibre
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexp : ∀ v, exponent v ≤ n)
    (honeLoss : ∀ v, (active C v).card ≤ n - exponent v + 1)
    (b : V) (d : Fin n → Bool) :
    Finset {w : Fin n → Bool //
      w ∈ netActualForwardReverseCollisionWords
        C exponent hexp honeLoss} :=
  Finset.univ.filter (fun s =>
    netCollisionCertifiedDiagonal C exponent hexp honeLoss s = d ∧
    (netCollisionCertifiedBridgeOwner C exponent hexp honeLoss s).1 = b)

/-- Genuine collision sources hitting target d whose original soft
bridge has forward-UPPER endpoint v. -/
noncomputable def netCollisionUpperVertexDiagonalFibre
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexp : ∀ v, exponent v ≤ n)
    (honeLoss : ∀ v, (active C v).card ≤ n - exponent v + 1)
    (v : V) (d : Fin n → Bool) :
    Finset {w : Fin n → Bool //
      w ∈ netActualForwardReverseCollisionWords
        C exponent hexp honeLoss} :=
  Finset.univ.filter (fun s =>
    netCollisionCertifiedDiagonal C exponent hexp honeLoss s = d ∧
    (netCollisionCertifiedBridgeOwner C exponent hexp honeLoss s).2 = v)

/-- Fixed-target, fixed lower bridge endpoint: the original REVERSE
hard colour is INJECTIVE on ACTUAL source words (even with differing
original hard source carriers). -/
theorem net_collision_same_diagonal_lower_star_reverse_colour_injective
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexp : ∀ v, exponent v ≤ n)
    (honeLoss : ∀ v, (active C v).card ≤ n - exponent v + 1)
    (b : V) (d : Fin n → Bool) :
    Function.Injective
      (fun s : {w : {u : Fin n → Bool //
        u ∈ netActualForwardReverseCollisionWords C exponent hexp honeLoss} //
          w ∈ netCollisionLowerVertexDiagonalFibre
            C exponent hexp honeLoss b d} =>
        strictDescentRigidPairColor C exponent hexp honeLoss
          (strictDescentRigidWordCarrier C exponent
            (netCollisionCertifiedReverseSource
              C exponent hexp honeLoss s.1))) := by
  intro s t hcr
  change strictDescentRigidPairColor C exponent hexp honeLoss
    (strictDescentRigidWordCarrier C exponent
      (netCollisionCertifiedReverseSource C exponent hexp honeLoss s.1)) =
    strictDescentRigidPairColor C exponent hexp honeLoss
    (strictDescentRigidWordCarrier C exponent
      (netCollisionCertifiedReverseSource C exponent hexp honeLoss t.1))
    at hcr
  have hs := (Finset.mem_filter.mp s.2).2
  have ht := (Finset.mem_filter.mp t.2).2
  change netCollisionCertifiedDiagonal C exponent hexp honeLoss s.1 = d ∧
    (netCollisionCertifiedBridgeOwner C exponent hexp honeLoss s.1).1 = b at hs
  change netCollisionCertifiedDiagonal C exponent hexp honeLoss t.1 = d ∧
    (netCollisionCertifiedBridgeOwner C exponent hexp honeLoss t.1).1 = b at ht
  have hdiag := hs.1.trans ht.1.symm
  have hb := hs.2.trans ht.2.symm
  have hcf := net_collision_equal_diagonal_same_lower_forward_colour_eq
    C exponent hexp honeLoss s.1 t.1 hdiag hb
  have hsupport :
      netCollisionCanonicalColourSupport C exponent hexp honeLoss s.1 =
      netCollisionCanonicalColourSupport C exponent hexp honeLoss t.1 := by
    unfold netCollisionCanonicalColourSupport
    rw [hcf, hcr]
  have heq := net_collision_canonical_support_fibre_injective
    C exponent hexp honeLoss s.1 t.1 hdiag hsupport
  exact Subtype.ext heq

/-- Fixed-target, fixed upper bridge endpoint: the original FORWARD
hard colour is INJECTIVE on ACTUAL source words. -/
theorem net_collision_same_diagonal_upper_star_forward_colour_injective
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexp : ∀ v, exponent v ≤ n)
    (honeLoss : ∀ v, (active C v).card ≤ n - exponent v + 1)
    (v : V) (d : Fin n → Bool) :
    Function.Injective
      (fun s : {w : {u : Fin n → Bool //
        u ∈ netActualForwardReverseCollisionWords C exponent hexp honeLoss} //
          w ∈ netCollisionUpperVertexDiagonalFibre
            C exponent hexp honeLoss v d} =>
        transportablePairColor C
          (transportableWordCarrier C
            (netCollisionCertifiedForwardSource
              C exponent hexp honeLoss s.1))) := by
  intro s t hcf
  change transportablePairColor C
    (transportableWordCarrier C
      (netCollisionCertifiedForwardSource C exponent hexp honeLoss s.1)) =
    transportablePairColor C
    (transportableWordCarrier C
      (netCollisionCertifiedForwardSource C exponent hexp honeLoss t.1))
    at hcf
  have hs := (Finset.mem_filter.mp s.2).2
  have ht := (Finset.mem_filter.mp t.2).2
  change netCollisionCertifiedDiagonal C exponent hexp honeLoss s.1 = d ∧
    (netCollisionCertifiedBridgeOwner C exponent hexp honeLoss s.1).2 = v at hs
  change netCollisionCertifiedDiagonal C exponent hexp honeLoss t.1 = d ∧
    (netCollisionCertifiedBridgeOwner C exponent hexp honeLoss t.1).2 = v at ht
  have hdiag := hs.1.trans ht.1.symm
  have hv := hs.2.trans ht.2.symm
  have hcr := net_collision_equal_diagonal_same_upper_reverse_colour_eq
    C exponent hexp honeLoss s.1 t.1 hdiag hv
  have hsupport :
      netCollisionCanonicalColourSupport C exponent hexp honeLoss s.1 =
      netCollisionCanonicalColourSupport C exponent hexp honeLoss t.1 := by
    unfold netCollisionCanonicalColourSupport
    rw [hcf, hcr]
  have heq := net_collision_canonical_support_fibre_injective
    C exponent hexp honeLoss s.1 t.1 hdiag hsupport
  exact Subtype.ext heq

/-- A fixed lower endpoint's ACTUAL same-diagonal source count
is bounded by the number of its retained-INACTIVE colours, not by
the global number of other bridge vertices or by 2^inactive. -/
theorem net_collision_lower_star_target_fibre_card_le_inactive
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexp : ∀ v, exponent v ≤ n)
    (honeLoss : ∀ v, (active C v).card ≤ n - exponent v + 1)
    (b : V) (d : Fin n → Bool) :
    (netCollisionLowerVertexDiagonalFibre C exponent hexp honeLoss b d).card ≤
      ((Finset.univ : Finset (Fin n)) \ retainedActive C b).card := by
  classical
  let S := {w : Fin n → Bool //
    w ∈ netActualForwardReverseCollisionWords C exponent hexp honeLoss}
  let F : Finset S :=
    netCollisionLowerVertexDiagonalFibre C exponent hexp honeLoss b d
  let f : {s : S // s ∈ F} → Fin n :=
    fun s => strictDescentRigidPairColor C exponent hexp honeLoss
      (strictDescentRigidWordCarrier C exponent
        (netCollisionCertifiedReverseSource C exponent hexp honeLoss s.1))
  have hinj : Function.Injective f :=
    net_collision_same_diagonal_lower_star_reverse_colour_injective
      C exponent hexp honeLoss b d
  have hsub : (Finset.univ : Finset {s : S // s ∈ F}).image f ⊆
      (Finset.univ : Finset (Fin n)) \ retainedActive C b := by
    intro e he
    obtain ⟨s, _, rfl⟩ := Finset.mem_image.mp he
    have hs := (Finset.mem_filter.mp s.2).2
    change netCollisionCertifiedDiagonal C exponent hexp honeLoss s.1 = d ∧
      (netCollisionCertifiedBridgeOwner C exponent hexp honeLoss s.1).1 = b
      at hs
    let q := strictDescentRigidWordCarrier C exponent
      (netCollisionCertifiedReverseSource C exponent hexp honeLoss s.1)
    have hnot : strictDescentRigidPairColor C exponent hexp honeLoss q ∉
        retainedActive C q.1.1 :=
      (strictDescentRigidPairColor_spec C exponent hexp honeLoss q).2
    have hendpoint :
        (netCollisionCertifiedBridgeOwner C exponent hexp honeLoss s.1).1 =
        q.1.1 := rfl
    have hb : q.1.1 = b := hendpoint.symm.trans hs.2
    exact Finset.mem_sdiff.mpr
      ⟨Finset.mem_univ _, by simpa only [hb] using hnot⟩
  change F.card ≤ ((Finset.univ : Finset (Fin n)) \ retainedActive C b).card
  calc
    F.card = (Finset.univ : Finset {s : S // s ∈ F}).card := by simp
    _ = ((Finset.univ : Finset {s : S // s ∈ F}).image f).card :=
      (Finset.card_image_of_injective _ hinj).symm
    _ ≤ _ := Finset.card_le_card hsub

/-- The analogous sharp fixed-upper-endpoint count. -/
theorem net_collision_upper_star_target_fibre_card_le_inactive
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexp : ∀ v, exponent v ≤ n)
    (honeLoss : ∀ v, (active C v).card ≤ n - exponent v + 1)
    (v : V) (d : Fin n → Bool) :
    (netCollisionUpperVertexDiagonalFibre C exponent hexp honeLoss v d).card ≤
      ((Finset.univ : Finset (Fin n)) \ retainedActive C v).card := by
  classical
  let S := {w : Fin n → Bool //
    w ∈ netActualForwardReverseCollisionWords C exponent hexp honeLoss}
  let F : Finset S :=
    netCollisionUpperVertexDiagonalFibre C exponent hexp honeLoss v d
  let f : {s : S // s ∈ F} → Fin n :=
    fun s => transportablePairColor C
      (transportableWordCarrier C
        (netCollisionCertifiedForwardSource C exponent hexp honeLoss s.1))
  have hinj : Function.Injective f :=
    net_collision_same_diagonal_upper_star_forward_colour_injective
      C exponent hexp honeLoss v d
  have hsub : (Finset.univ : Finset {s : S // s ∈ F}).image f ⊆
      (Finset.univ : Finset (Fin n)) \ retainedActive C v := by
    intro e he
    obtain ⟨s, _, rfl⟩ := Finset.mem_image.mp he
    have hs := (Finset.mem_filter.mp s.2).2
    change netCollisionCertifiedDiagonal C exponent hexp honeLoss s.1 = d ∧
      (netCollisionCertifiedBridgeOwner C exponent hexp honeLoss s.1).2 = v
      at hs
    let p := transportableWordCarrier C
      (netCollisionCertifiedForwardSource C exponent hexp honeLoss s.1)
    have hnot : transportablePairColor C p ∉ retainedActive C p.1.2 :=
      (transportablePairColor_spec C p).2
    have hendpoint :
        (netCollisionCertifiedBridgeOwner C exponent hexp honeLoss s.1).2 =
        p.1.2 := rfl
    have hv : p.1.2 = v := hendpoint.symm.trans hs.2
    exact Finset.mem_sdiff.mpr
      ⟨Finset.mem_univ _, by simpa only [hv] using hnot⟩
  change F.card ≤ ((Finset.univ : Finset (Fin n)) \ retainedActive C v).card
  calc
    F.card = (Finset.univ : Finset {s : S // s ∈ F}).card := by simp
    _ = ((Finset.univ : Finset {s : S // s ∈ F}).image f).card :=
      (Finset.card_image_of_injective _ hinj).symm
    _ ≤ _ := Finset.card_le_card hsub

#print axioms net_collision_same_diagonal_lower_star_reverse_colour_injective
#print axioms net_collision_same_diagonal_upper_star_forward_colour_injective
#print axioms net_collision_lower_star_target_fibre_card_le_inactive
#print axioms net_collision_upper_star_target_fibre_card_le_inactive

end OrderedEdgeColoring
end JSP000404Research
