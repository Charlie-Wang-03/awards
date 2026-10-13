import JSP000404Research.ResidualNetCollisionExactHammingObstruction
import Mathlib.Tactic

/-!
# Exact diagonal-collision colour intersection versus Hamming distance

The earlier certificate proves disagreement support equals the symmetric
difference of the two unordered original forward/reverse colour pairs.
Here we convert that Boolean set equality into the exact conservation

    HammingDistance(w,z) + 2 * |ColourPair(w) ∩ ColourPair(z)| = 4.

For genuine NET collisions, every canonical pair has TWO distinct colours.
Consequently the Hamming-two case has exactly ONE common colour, while the
Hamming-four case has NO common colour. These are honest necessary
constraints, not AngleCap exclusions or claimed hole payments.
-/

namespace JSP000404Research
namespace OrderedEdgeColoring

/-- Exact cardinal conservation for two abstract 2-element sets. -/
theorem two_two_support_symmetric_difference_intersection_card
    {α : Type*} [DecidableEq α]
    (A B : Finset α) (hA : A.card = 2) (hB : B.card = 2) :
    ((A \ B) ∪ (B \ A)).card + 2 * (A ∩ B).card = 4 := by
  classical
  have hsplitA : A = (A \ B) ∪ (A ∩ B) := by
    ext e
    simp only [Finset.mem_union, Finset.mem_sdiff, Finset.mem_inter]
    tauto
  have hsplitB : B = (B \ A) ∪ (A ∩ B) := by
    ext e
    simp only [Finset.mem_union, Finset.mem_sdiff, Finset.mem_inter]
    tauto
  have hdisA : Disjoint (A \ B) (A ∩ B) := by
    apply Finset.disjoint_left.mpr
    intro e he hf
    exact (Finset.mem_sdiff.mp he).2 (Finset.mem_inter.mp hf).2
  have hdisB : Disjoint (B \ A) (A ∩ B) := by
    apply Finset.disjoint_left.mpr
    intro e he hf
    exact (Finset.mem_sdiff.mp he).2 (Finset.mem_inter.mp hf).1
  have hdis : Disjoint (A \ B) (B \ A) := by
    apply Finset.disjoint_left.mpr
    intro e he hf
    exact (Finset.mem_sdiff.mp he).2 (Finset.mem_sdiff.mp hf).1
  have ha : A.card = (A \ B).card + (A ∩ B).card := by
    calc
      A.card = ((A \ B) ∪ (A ∩ B)).card :=
        congrArg Finset.card hsplitA
      _ = (A \ B).card + (A ∩ B).card :=
        Finset.card_union_of_disjoint hdisA
  have hb : B.card = (B \ A).card + (A ∩ B).card := by
    calc
      B.card = ((B \ A) ∪ (A ∩ B)).card :=
        congrArg Finset.card hsplitB
      _ = (B \ A).card + (A ∩ B).card :=
        Finset.card_union_of_disjoint hdisB
  have hd : ((A \ B) ∪ (B \ A)).card =
      (A \ B).card + (B \ A).card :=
    Finset.card_union_of_disjoint hdis
  omega

/-- For ANY two genuine NET source words with a common certified
diagonal, Hamming distance PLUS TWICE the number of shared
canonical original transport colours is precisely four. -/
theorem net_collision_equal_diagonal_hamming_plus_twice_common_eq_four
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexp : ∀ v, exponent v ≤ n)
    (honeLoss : ∀ v, (active C v).card ≤ n - exponent v + 1)
    (s t : {w : Fin n → Bool //
      w ∈ netActualForwardReverseCollisionWords
        C exponent hexp honeLoss})
    (heq : netCollisionCertifiedDiagonal C exponent hexp honeLoss s =
      netCollisionCertifiedDiagonal C exponent hexp honeLoss t) :
    (Finset.univ.filter (fun e : Fin n => s.1 e ≠ t.1 e)).card +
      2 * (netCollisionCanonicalColourSupport C exponent hexp honeLoss s ∩
        netCollisionCanonicalColourSupport C exponent hexp honeLoss t).card =
      4 := by
  classical
  let A := netCollisionCanonicalColourSupport C exponent hexp honeLoss s
  let B := netCollisionCanonicalColourSupport C exponent hexp honeLoss t
  have hs := net_collision_certified_forward_reverse_colours_distinct
    C exponent hexp honeLoss s
  have ht := net_collision_certified_forward_reverse_colours_distinct
    C exponent hexp honeLoss t
  have hA : A.card = 2 := by
    simp [A, netCollisionCanonicalColourSupport, hs]
  have hB : B.card = 2 := by
    simp [B, netCollisionCanonicalColourSupport, ht]
  have hdiff := net_collision_canonical_diagonal_exact_difference_support
    C exponent hexp honeLoss s t heq
  change (Finset.univ.filter (fun e : Fin n => s.1 e ≠ t.1 e)) =
    (A \ B) ∪ (B \ A) at hdiff
  rw [hdiff]
  exact two_two_support_symmetric_difference_intersection_card
    A B hA hB

/-- Exact two-bit case: the canonical transport-colour pairs
share precisely one colour (one and not both). -/
theorem net_collision_equal_diagonal_two_bits_iff_one_common_colour
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexp : ∀ v, exponent v ≤ n)
    (honeLoss : ∀ v, (active C v).card ≤ n - exponent v + 1)
    (s t : {w : Fin n → Bool //
      w ∈ netActualForwardReverseCollisionWords
        C exponent hexp honeLoss})
    (heq : netCollisionCertifiedDiagonal C exponent hexp honeLoss s =
      netCollisionCertifiedDiagonal C exponent hexp honeLoss t) :
    (Finset.univ.filter (fun e : Fin n => s.1 e ≠ t.1 e)).card = 2 ↔
      (netCollisionCanonicalColourSupport C exponent hexp honeLoss s ∩
        netCollisionCanonicalColourSupport C exponent hexp honeLoss t).card =
        1 := by
  have h := net_collision_equal_diagonal_hamming_plus_twice_common_eq_four
    C exponent hexp honeLoss s t heq
  omega

/-- Exact four-bit case: the canonical transport-colour pairs
are DISJOINT. -/
theorem net_collision_equal_diagonal_four_bits_iff_disjoint_colours
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexp : ∀ v, exponent v ≤ n)
    (honeLoss : ∀ v, (active C v).card ≤ n - exponent v + 1)
    (s t : {w : Fin n → Bool //
      w ∈ netActualForwardReverseCollisionWords
        C exponent hexp honeLoss})
    (heq : netCollisionCertifiedDiagonal C exponent hexp honeLoss s =
      netCollisionCertifiedDiagonal C exponent hexp honeLoss t) :
    (Finset.univ.filter (fun e : Fin n => s.1 e ≠ t.1 e)).card = 4 ↔
      Disjoint
        (netCollisionCanonicalColourSupport C exponent hexp honeLoss s)
        (netCollisionCanonicalColourSupport C exponent hexp honeLoss t) := by
  classical
  have h := net_collision_equal_diagonal_hamming_plus_twice_common_eq_four
    C exponent hexp honeLoss s t heq
  constructor
  · intro hfour
    have hz : (netCollisionCanonicalColourSupport C exponent hexp honeLoss s ∩
      netCollisionCanonicalColourSupport C exponent hexp honeLoss t).card =
        0 := by omega
    exact Finset.disjoint_iff_inter_eq_empty.mpr (Finset.card_eq_zero.mp hz)
  · intro hdis
    have hz : (netCollisionCanonicalColourSupport C exponent hexp honeLoss s ∩
      netCollisionCanonicalColourSupport C exponent hexp honeLoss t).card =
        0 := by
      rw [Finset.disjoint_iff_inter_eq_empty.mp hdis]
      simp
    omega

#print axioms two_two_support_symmetric_difference_intersection_card
#print axioms net_collision_equal_diagonal_hamming_plus_twice_common_eq_four
#print axioms net_collision_equal_diagonal_two_bits_iff_one_common_colour
#print axioms net_collision_equal_diagonal_four_bits_iff_disjoint_colours

end OrderedEdgeColoring
end JSP000404Research
