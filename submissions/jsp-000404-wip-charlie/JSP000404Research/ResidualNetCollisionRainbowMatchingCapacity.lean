import JSP000404Research.ResidualNetCollisionMaximumMatchingPayment
import Mathlib.Tactic

/-!
# Exact-shell rainbow matching obstruction for true NET duplicate fibres

An ordinary target-exact slot matching cannot capture the previously
certified UNIQUE unordered two-colour support of every actual source
at a fixed diagonal. Different candidate edges may use different
vertex slots but the SAME unordered pair of flip colours, and hence
cannot both be genuine same-diagonal NET sources.

Here a rainbow matching is an admissible bipartite matching with
pairwise DISTINCT unordered colour supports. All true source fibres
embed cardinality-preservingly into rainbow matchings. This sharpens
the ordinary matching upper bound without classifying graph edges as
true holes or separately unreserved dyadic surplus.

The graph-colour rainbow matching number is an explicit finite
maximum. A SMALL upper bound from genuine geometry, and the global
six-source payment, remain open.
-/

namespace JSP000404Research
namespace OrderedEdgeColoring

/-- A candidate original bridge edge's unordered transport flip
colours, deliberately ordered forward then reverse to match the
source-native canonical colour-support definition. -/
noncomputable def targetExactShellEdgeColourSupport
    {V : Type*} {n : ℕ}
    (e : (V × Fin n) × (V × Fin n)) : Finset (Fin n) :=
  {e.2.2, e.1.2}

/-- A finite candidate edge set is an actual-source-compatible
rainbow matching when no two selected edges reuse a lower slot,
an upper slot, OR the same unordered original flip-colour support. -/
noncomputable def targetExactShellRainbowMatching
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ) (d : Fin n → Bool)
    (M : Finset ((V × Fin n) × (V × Fin n))) : Prop :=
  M ⊆ targetExactShellSlotEdges C exponent d ∧
  (∀ e ∈ M, ∀ f ∈ M, e.1 = f.1 → e = f) ∧
  (∀ e ∈ M, ∀ f ∈ M, e.2 = f.2 → e = f) ∧
  (∀ e ∈ M, ∀ f ∈ M,
    targetExactShellEdgeColourSupport e =
      targetExactShellEdgeColourSupport f → e = f)

/-- EVERY true same-diagonal NET source fibre yields a matching of
the SAME cardinality whose different edges have different original
unordered two-flip-colour supports. No unproved AngleCap bound is used. -/
theorem net_collision_target_fibre_has_exact_rainbow_matching
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexp : ∀ v, exponent v ≤ n)
    (honeLoss : ∀ v, (active C v).card ≤ n - exponent v + 1)
    (d : Fin n → Bool) :
    ∃ M : Finset ((V × Fin n) × (V × Fin n)),
      targetExactShellRainbowMatching C exponent d M ∧
      M.card =
        (netCollisionCertifiedDiagonalFibre C exponent hexp honeLoss d).card := by
  classical
  let S := {w : Fin n → Bool //
    w ∈ netActualForwardReverseCollisionWords C exponent hexp honeLoss}
  let F : Finset S :=
    netCollisionCertifiedDiagonalFibre C exponent hexp honeLoss d
  let g : {s : S // s ∈ F} → ((V × Fin n) × (V × Fin n)) :=
    fun s =>
      (netCollisionCertifiedLowerColourSlot C exponent hexp honeLoss s.1,
       netCollisionCertifiedUpperColourSlot C exponent hexp honeLoss s.1)
  let M := (Finset.univ : Finset {s : S // s ∈ F}).image g
  have htarget (s : {s : S // s ∈ F}) :
      netCollisionCertifiedDiagonal C exponent hexp honeLoss s.1 = d :=
    (Finset.mem_filter.mp s.2).2
  have hleft : Function.Injective (fun s : {s : S // s ∈ F} => (g s).1) := by
    intro s t h
    apply Subtype.ext
    exact net_collision_same_target_lower_slot_injective
      C exponent hexp honeLoss s.1 t.1
      ((htarget s).trans (htarget t).symm) h
  have hright : Function.Injective (fun s : {s : S // s ∈ F} => (g s).2) := by
    intro s t h
    apply Subtype.ext
    exact net_collision_same_target_upper_slot_injective
      C exponent hexp honeLoss s.1 t.1
      ((htarget s).trans (htarget t).symm) h
  have hinj : Function.Injective g := by
    intro s t h
    exact hleft (congrArg Prod.fst h)
  refine ⟨M, ?_, ?_⟩
  · refine ⟨?_, ?_, ?_, ?_⟩
    · intro e he
      obtain ⟨s, _, rfl⟩ := Finset.mem_image.mp he
      have hmem :=
        net_collision_actual_pair_mem_exact_shell_slot_edges
          C exponent hexp honeLoss s.1
      rw [htarget s] at hmem
      exact hmem
    · intro e he f hf h
      obtain ⟨s, _, rfl⟩ := Finset.mem_image.mp he
      obtain ⟨t, _, rfl⟩ := Finset.mem_image.mp hf
      have hs : s = t := hleft h
      rw [hs]
    · intro e he f hf h
      obtain ⟨s, _, rfl⟩ := Finset.mem_image.mp he
      obtain ⟨t, _, rfl⟩ := Finset.mem_image.mp hf
      have hs : s = t := hright h
      rw [hs]
    · intro e he f hf h
      obtain ⟨s, _, rfl⟩ := Finset.mem_image.mp he
      obtain ⟨t, _, rfl⟩ := Finset.mem_image.mp hf
      have hsame :
          netCollisionCanonicalColourSupport C exponent hexp honeLoss s.1 =
          netCollisionCanonicalColourSupport C exponent hexp honeLoss t.1 := by
        change netCollisionCanonicalColourSupport
          C exponent hexp honeLoss s.1 =
          netCollisionCanonicalColourSupport
          C exponent hexp honeLoss t.1 at h
        exact h
      have hst : s.1 = t.1 :=
        net_collision_canonical_support_fibre_injective
          C exponent hexp honeLoss s.1 t.1
          ((htarget s).trans (htarget t).symm) hsame
      have hs : s = t := Subtype.ext hst
      rw [hs]
  · change ((Finset.univ : Finset {s : S // s ∈ F}).image g).card =
      F.card
    calc
      ((Finset.univ : Finset {s : S // s ∈ F}).image g).card =
          (Finset.univ : Finset {s : S // s ∈ F}).card :=
        Finset.card_image_of_injective _ hinj
      _ = F.card := by simp

/-- Explicit maximum cardinality among all feasible finite RAINBOW
matchings. It cannot exceed the ordinary matching number. -/
noncomputable def targetExactShellRainbowMatchingNumber
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ) (d : Fin n → Bool) : ℕ := by
  classical
  exact
    ((Finset.univ : Finset (Finset ((V × Fin n) × (V × Fin n)))).filter
      (targetExactShellRainbowMatching C exponent d)).sup Finset.card

theorem exact_shell_rainbow_matching_card_le_rainbow_number
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ) (d : Fin n → Bool)
    (M : Finset ((V × Fin n) × (V × Fin n)))
    (hM : targetExactShellRainbowMatching C exponent d M) :
    M.card ≤ targetExactShellRainbowMatchingNumber C exponent d := by
  classical
  unfold targetExactShellRainbowMatchingNumber
  apply Finset.le_sup
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hM⟩

theorem exact_shell_rainbow_matching_number_le_ordinary_matching_number
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ) (d : Fin n → Bool) :
    targetExactShellRainbowMatchingNumber C exponent d ≤
      targetExactShellSlotMatchingNumber C exponent d := by
  classical
  unfold targetExactShellRainbowMatchingNumber
  apply Finset.sup_le
  intro M hM
  obtain ⟨_, hsub, hl, hr, _⟩ := Finset.mem_filter.mp hM
  exact exact_shell_slot_matching_card_le_matching_number
    C exponent d M hsub hl hr

theorem net_collision_target_fibre_card_le_rainbow_matching_number
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexp : ∀ v, exponent v ≤ n)
    (honeLoss : ∀ v, (active C v).card ≤ n - exponent v + 1)
    (d : Fin n → Bool) :
    (netCollisionCertifiedDiagonalFibre C exponent hexp honeLoss d).card ≤
      targetExactShellRainbowMatchingNumber C exponent d := by
  obtain ⟨M, hM, hcard⟩ :=
    net_collision_target_fibre_has_exact_rainbow_matching
      C exponent hexp honeLoss d
  rw [← hcard]
  exact exact_shell_rainbow_matching_card_le_rainbow_number
    C exponent d M hM

theorem net_collision_duplicate_debt_le_sum_rainbow_matching_excess
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexp : ∀ v, exponent v ≤ n)
    (honeLoss : ∀ v, (active C v).card ≤ n - exponent v + 1) :
    netCollisionCertifiedDuplicateDebt C exponent hexp honeLoss ≤
      ∑ d ∈ netCollisionCertifiedDiagonalWords C exponent hexp honeLoss,
        (targetExactShellRainbowMatchingNumber C exponent d - 1) := by
  rw [net_collision_certified_duplicate_debt_eq_sum_fibre_excess
    C exponent hexp honeLoss]
  apply Finset.sum_le_sum
  intro d hd
  have hfibre :=
    net_collision_target_fibre_card_le_rainbow_matching_number
      C exponent hexp honeLoss d
  omega

theorem net_mobile_mass_le_holes_covered_rainbow_matching_excess
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexp : ∀ v, exponent v ≤ n)
    (honeLoss : ∀ v, (active C v).card ≤ n - exponent v + 1) :
    (netTransportableHardWords C exponent).card +
      (netStrictDescentRigidWords C exponent).card ≤
      (singletonCompletionWords C).card +
      (softOverlapCompletionWords C).card +
      ((Finset.univ : Finset (Fin n → Bool)) \
        coveredCompletionWords C).card +
      (netCollisionCertifiedCoveredDiagonals
        C exponent hexp honeLoss).card +
      (∑ d ∈ netCollisionCertifiedDiagonalWords C exponent hexp honeLoss,
        (targetExactShellRainbowMatchingNumber C exponent d - 1)) := by
  have hmobile :=
    net_mobile_mass_le_singleton_soft_holes_blockers_duplicates
      C exponent hexp honeLoss
  have hrainbow :=
    net_collision_duplicate_debt_le_sum_rainbow_matching_excess
      C exponent hexp honeLoss
  omega

#print axioms net_collision_target_fibre_has_exact_rainbow_matching
#print axioms exact_shell_rainbow_matching_card_le_rainbow_number
#print axioms exact_shell_rainbow_matching_number_le_ordinary_matching_number
#print axioms net_collision_target_fibre_card_le_rainbow_matching_number
#print axioms net_collision_duplicate_debt_le_sum_rainbow_matching_excess
#print axioms net_mobile_mass_le_holes_covered_rainbow_matching_excess

end OrderedEdgeColoring
end JSP000404Research
