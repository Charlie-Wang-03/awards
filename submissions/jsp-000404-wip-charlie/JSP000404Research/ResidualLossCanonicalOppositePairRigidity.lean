import JSP000404Research.ResidualLossCanonicalRecordDebtEquiv
import JSP000404Research.BooleanFlipCore
import Mathlib.Tactic

/-!
# Original earliest-prior duplicate-debt opposite-target COORDINATE PAIR RIGIDITY

In the genuine open n>=3 branch, the defect Ddup - |O| measures the
multiplicity of the SAME opposite corner across distinct original
earliest-prior source records. Two records with the SAME ordered (later,
earlier) coordinate pair cannot collide under double-flip, because
each fixed-coordinate Boolean flip is an involution/injection.

Therefore every nontrivial reused opposite target must arise from
DISTINCT original coordinate pairs, not from within-pair word reuse.
For n=3 two distinct ordered 2-subsets of three colours intersect
necessarily in at least one coordinate. This sharply isolates the
first open combinatorial motif without creating true hole credits.
-/

namespace JSP000404Research
namespace OrderedEdgeColoring

/-- The two-bit opposite map is injective when the ordered pair of
coordinates is fixed. The statement is purely Boolean and works
even before imposing original source eligibility. -/
theorem loss_opposite_same_coordinate_pair_injective
    {n : ℕ}
    (a b : Fin n × Fin n × (Fin n → Bool))
    (hc : a.1 = b.1)
    (hd : a.2.1 = b.2.1)
    (hopposite :
      flipBoolWordAt (flipBoolWordAt a.2.2 a.1) a.2.1 =
      flipBoolWordAt (flipBoolWordAt b.2.2 b.1) b.2.1) :
    a = b := by
  have hword : a.2.2 = b.2.2 := by
    rw [← hc, ← hd] at hopposite
    exact (flipBoolWordAt_injective a.1)
      ((flipBoolWordAt_injective a.2.1) hopposite)
  apply Prod.ext
  · exact hc
  · apply Prod.ext
    · exact hd
    · exact hword

/-- In the exact ORIGINAL earliest-prior duplicate-debt family,
a genuine repeated opposite target always uses DISTINCT ordered
coordinate pairs. Swapping the pair orientation is already excluded
by the canonical j<i condition. -/
theorem actual_loss_reused_opposite_requires_distinct_coordinate_pairs
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ) (choice : V → Fin n)
    (a b : Fin n × Fin n × (Fin n → Bool))
    (ha : a ∈ actualEarliestLossCollisionRecords C exponent choice)
    (hb : b ∈ actualEarliestLossCollisionRecords C exponent choice)
    (hne : a ≠ b)
    (hopposite :
      flipBoolWordAt (flipBoolWordAt a.2.2 a.1) a.2.1 =
      flipBoolWordAt (flipBoolWordAt b.2.2 b.1) b.2.1) :
    a.1 ≠ b.1 ∨ a.2.1 ≠ b.2.1 := by
  by_contra h
  push_neg at h
  exact hne
    (loss_opposite_same_coordinate_pair_injective a b h.1 h.2 hopposite)

/-- Among exactly THREE Boolean colours, any two genuine prior-first
ordered coordinate pairs (j<i) must share at least one colour.
This holds WITHOUT a true-hole or matching hypothesis. -/
theorem actual_three_colour_earliest_pairs_intersect
    {V : Type*} [LinearOrder V] [Fintype V]
    (C : OrderedEdgeColoring V (3 + 1))
    (exponent : V → ℕ) (choice : V → Fin 3)
    (a b : Fin 3 × Fin 3 × (Fin 3 → Bool))
    (ha : a ∈ actualEarliestLossCollisionRecords C exponent choice)
    (hb : b ∈ actualEarliestLossCollisionRecords C exponent choice) :
    a.1 = b.1 ∨ a.1 = b.2.1 ∨
      a.2.1 = b.1 ∨ a.2.1 = b.2.1 := by
  have hltA :=
    (actual_earliest_loss_collision_record_valid
      C exponent choice a ha).2.1
  have hltB :=
    (actual_earliest_loss_collision_record_valid
      C exponent choice b hb).2.1
  have hAc := a.1.isLt
  have hAd := a.2.1.isLt
  have hBc := b.1.isLt
  have hBd := b.2.1.isLt
  omega

/-- In the first genuinely OPEN colour width n=3, reused opposite
targets can only arise from DISTINCT, INTERSECTING actual coordinate
pairs. This excludes disjoint-pair and same-pair reuse motifs. It does
NOT rule out the surviving one-common-coordinate motif. -/
theorem actual_three_colour_opposite_reuse_only_intersecting_distinct_pairs
    {V : Type*} [LinearOrder V] [Fintype V]
    (C : OrderedEdgeColoring V (3 + 1))
    (exponent : V → ℕ) (choice : V → Fin 3)
    (a b : Fin 3 × Fin 3 × (Fin 3 → Bool))
    (ha : a ∈ actualEarliestLossCollisionRecords C exponent choice)
    (hb : b ∈ actualEarliestLossCollisionRecords C exponent choice)
    (hne : a ≠ b)
    (hopposite :
      flipBoolWordAt (flipBoolWordAt a.2.2 a.1) a.2.1 =
      flipBoolWordAt (flipBoolWordAt b.2.2 b.1) b.2.1) :
    (a.1 ≠ b.1 ∨ a.2.1 ≠ b.2.1) ∧
      (a.1 = b.1 ∨ a.1 = b.2.1 ∨
        a.2.1 = b.1 ∨ a.2.1 = b.2.1) := by
  exact ⟨
    actual_loss_reused_opposite_requires_distinct_coordinate_pairs
      C exponent choice a b ha hb hne hopposite,
    actual_three_colour_earliest_pairs_intersect
      C exponent choice a b ha hb⟩

#print axioms loss_opposite_same_coordinate_pair_injective
#print axioms actual_loss_reused_opposite_requires_distinct_coordinate_pairs
#print axioms actual_three_colour_earliest_pairs_intersect
#print axioms actual_three_colour_opposite_reuse_only_intersecting_distinct_pairs

end OrderedEdgeColoring
end JSP000404Research
