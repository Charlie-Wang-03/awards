import JSP000404Research.ResidualNetCollisionRainbowRedundancyAudit
import Mathlib.Tactic

/-!
# Exact target-local Hamming-two SOFT shadow sphere capacity

The previous fixed-target edge->soft-word injection bounded every
eligible exact-shell edge set by ALL soft overlap words globally.
However EVERY candidate shadow is exactly TWO Boolean flips away
from the candidate target diagonal d.

Restrict the target's resource pool to actual SOFT words at Hamming
distance exactly TWO from d. The exact-slot graph edges inject into
this SMALLER local sphere. In particular actual NET duplicate fibres
are bounded by the local source-compatible covered-word sphere,
and the duplicate debt can be controlled target by target.

This remains a covered-word accounting certificate, NOT a payment
by true Boolean holes or unreserved dyadic surplus. There is still
no global cross-target injectivity.
-/

namespace JSP000404Research
namespace OrderedEdgeColoring

/-- Actual globally soft-overlapped words whose Boolean Hamming
distance from the chosen target d is EXACTLY TWO. -/
noncomputable def targetHammingTwoSoftOverlapWords
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (d : Fin n → Bool) : Finset (Fin n → Bool) := by
  classical
  exact (softOverlapCompletionWords C).filter
    (fun s => (Finset.univ.filter (fun i : Fin n => s i ≠ d i)).card = 2)

/-- Two distinct coordinate flips have Hamming difference set
exactly equal to the selected unordered two-coordinate support. -/
theorem two_flip_word_exact_hamming_two_support
    {n : ℕ} (d : Fin n → Bool) (a b : Fin n)
    (hab : a ≠ b) :
    (Finset.univ.filter (fun i : Fin n =>
      flipCompletionWord a (flipCompletionWord b d) i ≠ d i)) =
      ({a, b} : Finset (Fin n)) := by
  classical
  ext i
  simp only [Finset.mem_filter, Finset.mem_univ, true_and,
    Finset.mem_insert, Finset.mem_singleton]
  rw [distinct_two_flip_coordinate_eval d a b i hab]
  by_cases hi : i = a ∨ i = b
  · cases d i <;> simp [hi]
  · simp [hi]

theorem two_flip_word_hamming_distance_two
    {n : ℕ} (d : Fin n → Bool) (a b : Fin n)
    (hab : a ≠ b) :
    (Finset.univ.filter (fun i : Fin n =>
      flipCompletionWord a (flipCompletionWord b d) i ≠ d i)).card = 2 := by
  rw [two_flip_word_exact_hamming_two_support d a b hab]
  simp [hab]

/-- The candidate shadow is an ACTUAL SOFT overlap completion word
in the two-bit Hamming sphere of its FIXED target diagonal. -/
theorem target_exact_shell_candidate_shadow_mem_local_soft_sphere
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ) (d : Fin n → Bool)
    (e : (V × Fin n) × (V × Fin n))
    (he : e ∈ targetExactShellSlotEdges C exponent d) :
    flipCompletionWord e.2.2 (flipCompletionWord e.1.2 d) ∈
      targetHammingTwoSoftOverlapWords C d := by
  classical
  apply Finset.mem_filter.mpr
  refine ⟨target_exact_shell_candidate_shadow_mem_soft_overlap
    C exponent d e he, ?_⟩
  exact two_flip_word_hamming_distance_two d e.2.2 e.1.2
    (target_exact_shell_candidate_edge_colours_distinct
      C exponent d e he)

/-- A fixed-target candidate graph injects into the target-local,
actual SOFT overlap Hamming-two sphere. This is stronger than the
global |E(d)| <= |all soft words| bound, without any additional
planar geometric premise. -/
theorem target_exact_shell_candidate_edges_card_le_local_soft_sphere
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ) (d : Fin n → Bool) :
    (targetExactShellSlotEdges C exponent d).card ≤
      (targetHammingTwoSoftOverlapWords C d).card := by
  classical
  let E := targetExactShellSlotEdges C exponent d
  let g : {e : (V × Fin n) × (V × Fin n) // e ∈ E} →
      (Fin n → Bool) :=
    fun e => flipCompletionWord e.1.2.2
      (flipCompletionWord e.1.1.2 d)
  have hinj : Function.Injective g := by
    intro e f h
    apply Subtype.ext
    exact target_exact_shell_candidate_shadow_injective_on_edges
      C exponent d e.1 f.1 e.2 f.2 h
  have hsub :
      (Finset.univ : Finset
        {e : (V × Fin n) × (V × Fin n) // e ∈ E}).image g ⊆
        targetHammingTwoSoftOverlapWords C d := by
    intro word hw
    obtain ⟨e, _, rfl⟩ := Finset.mem_image.mp hw
    exact target_exact_shell_candidate_shadow_mem_local_soft_sphere
      C exponent d e.1 e.2
  calc
    E.card =
        (Finset.univ : Finset
          {e : (V × Fin n) × (V × Fin n) // e ∈ E}).card := by simp
    _ = ((Finset.univ : Finset
          {e : (V × Fin n) × (V × Fin n) // e ∈ E}).image g).card := by
        symm
        exact Finset.card_image_of_injective _ hinj
    _ ≤ (targetHammingTwoSoftOverlapWords C d).card :=
      Finset.card_le_card hsub

/-- The new local sphere is a genuine subset of the total
ACTUAL SOFT overlap word inventory. -/
theorem target_hamming_two_soft_sphere_subset_soft
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (d : Fin n → Bool) :
    targetHammingTwoSoftOverlapWords C d ⊆
      softOverlapCompletionWords C := by
  intro s hs
  exact (Finset.mem_filter.mp hs).1

/-- UNCONDITIONAL local sphere capacity of an actual NET
collision source fibre; matching structure can further reduce it. -/
theorem net_collision_target_fibre_card_le_local_soft_sphere
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexp : ∀ v, exponent v ≤ n)
    (honeLoss : ∀ v, (active C v).card ≤ n - exponent v + 1)
    (d : Fin n → Bool) :
    (netCollisionCertifiedDiagonalFibre C exponent hexp honeLoss d).card ≤
      (targetHammingTwoSoftOverlapWords C d).card := by
  have hfibre :=
    net_collision_target_fibre_card_le_matching_number
      C exponent hexp honeLoss d
  have hgraph :
      targetExactShellSlotMatchingNumber C exponent d ≤
        (targetExactShellSlotEdges C exponent d).card := by
    classical
    unfold targetExactShellSlotMatchingNumber
    apply Finset.sup_le
    intro M hM
    exact Finset.card_le_card (Finset.mem_filter.mp hM).2.1
  have hshadow :=
    target_exact_shell_candidate_edges_card_le_local_soft_sphere
      C exponent d
  omega

/-- The sharp target-local soft sphere bound can be substituted
for the raw NET duplication budget. These are all COVERED
soft words; the global six-source payment is still open. -/
theorem net_collision_duplicate_debt_le_local_soft_sphere_excess
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexp : ∀ v, exponent v ≤ n)
    (honeLoss : ∀ v, (active C v).card ≤ n - exponent v + 1) :
    netCollisionCertifiedDuplicateDebt C exponent hexp honeLoss ≤
      ∑ d ∈ netCollisionCertifiedDiagonalWords C exponent hexp honeLoss,
        ((targetHammingTwoSoftOverlapWords C d).card - 1) := by
  rw [net_collision_certified_duplicate_debt_eq_sum_fibre_excess
    C exponent hexp honeLoss]
  apply Finset.sum_le_sum
  intro d hd
  have hbound :=
    net_collision_target_fibre_card_le_local_soft_sphere
      C exponent hexp honeLoss d
  omega

#print axioms two_flip_word_exact_hamming_two_support
#print axioms two_flip_word_hamming_distance_two
#print axioms target_exact_shell_candidate_shadow_mem_local_soft_sphere
#print axioms target_exact_shell_candidate_edges_card_le_local_soft_sphere
#print axioms target_hamming_two_soft_sphere_subset_soft
#print axioms net_collision_target_fibre_card_le_local_soft_sphere
#print axioms net_collision_duplicate_debt_le_local_soft_sphere_excess

end OrderedEdgeColoring
end JSP000404Research
