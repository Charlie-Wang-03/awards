import JSP000404Research.ResidualNetCollisionMatchingObstruction
import Mathlib.Tactic

/-!
# Entire actual NET source fibre embeds as a target-exact bipartite matching

Previous results proved that two distinct equal-target sources give two
disjoint slot edges. Here the ENTIRE finite source fibre is injected into
one pairwise slot-disjoint edge set, retaining its EXACT cardinality.

This proves a necessary matching obstruction of arbitrary size. Conditional
matching-number certificates can replace coarse endpoint-pool capacities
when bounding the REAL duplicate debt, but neither the candidate graph's
matching number nor any true-hole payment has been established from
planar AngleCap alone. No global six-source payment is claimed.
-/

namespace JSP000404Research
namespace OrderedEdgeColoring

/-- Every genuine same-diagonal NET source fibre has an EXACT
cardinality-preserving matching inside the geometrically permitted
target-exact shell-slot candidate graph. Distinct selected edges share
NEITHER a lower nor an upper vertex-colour slot. -/
theorem net_collision_target_fibre_has_exact_slot_matching
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexp : ∀ v, exponent v ≤ n)
    (honeLoss : ∀ v, (active C v).card ≤ n - exponent v + 1)
    (d : Fin n → Bool) :
    ∃ M : Finset ((V × Fin n) × (V × Fin n)),
      M ⊆ targetExactShellSlotEdges C exponent d ∧
      M.card =
        (netCollisionCertifiedDiagonalFibre C exponent hexp honeLoss d).card ∧
      (∀ e ∈ M, ∀ f ∈ M, e.1 = f.1 → e = f) ∧
      (∀ e ∈ M, ∀ f ∈ M, e.2 = f.2 → e = f) := by
  classical
  let S := {w : Fin n → Bool //
    w ∈ netActualForwardReverseCollisionWords C exponent hexp honeLoss}
  let F : Finset S :=
    netCollisionCertifiedDiagonalFibre C exponent hexp honeLoss d
  let left : S → V × Fin n :=
    netCollisionCertifiedLowerColourSlot C exponent hexp honeLoss
  let right : S → V × Fin n :=
    netCollisionCertifiedUpperColourSlot C exponent hexp honeLoss
  let edge : S → ((V × Fin n) × (V × Fin n)) :=
    fun s => (left s, right s)
  let g : {s : S // s ∈ F} → ((V × Fin n) × (V × Fin n)) :=
    fun s => edge s.1
  let M := (Finset.univ : Finset {s : S // s ∈ F}).image g
  have hleft : Function.Injective
      (fun s : {s : S // s ∈ F} => left s.1) := by
    intro s t heq
    apply Subtype.ext
    have hds :
        netCollisionCertifiedDiagonal C exponent hexp honeLoss s.1 = d :=
      (Finset.mem_filter.mp s.2).2
    have hdt :
        netCollisionCertifiedDiagonal C exponent hexp honeLoss t.1 = d :=
      (Finset.mem_filter.mp t.2).2
    exact net_collision_same_target_lower_slot_injective
      C exponent hexp honeLoss s.1 t.1 (hds.trans hdt.symm) heq
  have hright : Function.Injective
      (fun s : {s : S // s ∈ F} => right s.1) := by
    intro s t heq
    apply Subtype.ext
    have hds :
        netCollisionCertifiedDiagonal C exponent hexp honeLoss s.1 = d :=
      (Finset.mem_filter.mp s.2).2
    have hdt :
        netCollisionCertifiedDiagonal C exponent hexp honeLoss t.1 = d :=
      (Finset.mem_filter.mp t.2).2
    exact net_collision_same_target_upper_slot_injective
      C exponent hexp honeLoss s.1 t.1 (hds.trans hdt.symm) heq
  have hinj : Function.Injective g := by
    intro s t h
    apply hleft
    have heq : (edge s.1).1 = (edge t.1).1 := congrArg Prod.fst h
    exact heq
  refine ⟨M, ?_, ?_, ?_, ?_⟩
  · intro e he
    obtain ⟨s, _, rfl⟩ := Finset.mem_image.mp he
    have hd :
        netCollisionCertifiedDiagonal C exponent hexp honeLoss s.1 = d :=
      (Finset.mem_filter.mp s.2).2
    have hedge := net_collision_actual_pair_mem_exact_shell_slot_edges
      C exponent hexp honeLoss s.1
    rw [hd] at hedge
    exact hedge
  · change ((Finset.univ : Finset {s : S // s ∈ F}).image g).card =
      F.card
    calc
      ((Finset.univ : Finset {s : S // s ∈ F}).image g).card =
          (Finset.univ : Finset {s : S // s ∈ F}).card :=
        Finset.card_image_of_injective _ hinj
      _ = F.card := by simp
  · intro e he f hf h
    obtain ⟨s, _, rfl⟩ := Finset.mem_image.mp he
    obtain ⟨t, _, rfl⟩ := Finset.mem_image.mp hf
    have hs : s = t := hleft (by simpa only [g, edge] using h)
    rw [hs]
  · intro e he f hf h
    obtain ⟨s, _, rfl⟩ := Finset.mem_image.mp he
    obtain ⟨t, _, rfl⟩ := Finset.mem_image.mp hf
    have hs : s = t := hright (by simpa only [g, edge] using h)
    rw [hs]

/-- A bound certified for ALL matchings of the target-exact
candidate graph bounds the complete ACTUAL source fibre.
The matching bound is an extra hypothesis, not supplied by AngleCap. -/
theorem net_collision_target_fibre_card_le_of_matching_certificate
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexp : ∀ v, exponent v ≤ n)
    (honeLoss : ∀ v, (active C v).card ≤ n - exponent v + 1)
    (d : Fin n → Bool) (bound : ℕ)
    (hbound : ∀ M : Finset ((V × Fin n) × (V × Fin n)),
      M ⊆ targetExactShellSlotEdges C exponent d →
      (∀ e ∈ M, ∀ f ∈ M, e.1 = f.1 → e = f) →
      (∀ e ∈ M, ∀ f ∈ M, e.2 = f.2 → e = f) →
      M.card ≤ bound) :
    (netCollisionCertifiedDiagonalFibre C exponent hexp honeLoss d).card ≤
      bound := by
  obtain ⟨M, hsub, hcard, hl, hr⟩ :=
    net_collision_target_fibre_has_exact_slot_matching
      C exponent hexp honeLoss d
  rw [← hcard]
  exact hbound M hsub hl hr

/-- The exact duplicate-debt sum may be bounded by per-target
combinatorial matching certificates, avoiding implicit reutilization
of each endpoint slot. Existence of SMALL matching bounds and final
global geometric payment remain open. -/
theorem net_collision_duplicate_debt_le_matching_certificate_excess
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexp : ∀ v, exponent v ≤ n)
    (honeLoss : ∀ v, (active C v).card ≤ n - exponent v + 1)
    (bound : (Fin n → Bool) → ℕ)
    (hbound : ∀ d ∈ netCollisionCertifiedDiagonalWords
        C exponent hexp honeLoss,
      ∀ M : Finset ((V × Fin n) × (V × Fin n)),
        M ⊆ targetExactShellSlotEdges C exponent d →
        (∀ e ∈ M, ∀ f ∈ M, e.1 = f.1 → e = f) →
        (∀ e ∈ M, ∀ f ∈ M, e.2 = f.2 → e = f) →
        M.card ≤ bound d) :
    netCollisionCertifiedDuplicateDebt C exponent hexp honeLoss ≤
      ∑ d ∈ netCollisionCertifiedDiagonalWords C exponent hexp honeLoss,
        (bound d - 1) := by
  rw [net_collision_certified_duplicate_debt_eq_sum_fibre_excess
    C exponent hexp honeLoss]
  apply Finset.sum_le_sum
  intro d hd
  have hfibre :=
    net_collision_target_fibre_card_le_of_matching_certificate
      C exponent hexp honeLoss d (bound d) (hbound d hd)
  omega

#print axioms net_collision_target_fibre_has_exact_slot_matching
#print axioms net_collision_target_fibre_card_le_of_matching_certificate
#print axioms net_collision_duplicate_debt_le_matching_certificate_excess

end OrderedEdgeColoring
end JSP000404Research
