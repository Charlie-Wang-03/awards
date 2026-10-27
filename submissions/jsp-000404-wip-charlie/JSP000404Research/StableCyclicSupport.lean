import JSP000404Research.ZeroCarry
import Mathlib.Logic.Equiv.Fin.Rotate
import Mathlib.Data.Finset.Card
import Mathlib.Tactic

/-!
# Cyclic support bound for deletion-stable quotient profiles

For a quotient profile q : Fin m -> Nat, call the profile cyclically separated
when every positive entry is followed, under the canonical cyclic rotation, by
a zero entry.

This is the discrete support condition forced by zero gain at every incident
deletion: two cyclically adjacent positive quotients would give at least one
full exponent unit of merge gain.

The successor rotation injects the positive positions into zero positions.
Therefore

  2 * positiveSupport(q) <= m.

This is the basic cardinality constraint on every fully deletion-stable centre.
It is independent of the particular quotient sizes.
-/

namespace JSP000404Research

open scoped BigOperators

/- The finite-support definition and card lemma are provided by ZeroCarry
   for any finite index type; Fin m is an instance of that generic API. -/

/-- Every positive quotient is followed by a zero quotient in cyclic order. -/
def CyclicSeparatedPositive
    {m : ℕ} (q : Fin m → ℕ) : Prop :=
  ∀ i, q i ≠ 0 → q (finRotate m i) = 0

/-- The cyclic successor image of positive positions lies among zero
positions. -/
theorem rotate_positiveIndexSet_subset_zero
    {m : ℕ} (q : Fin m → ℕ)
    (hsep : CyclicSeparatedPositive q) :
    (positiveIndexSet q).image (finRotate m) ⊆
      (Finset.univ : Finset (Fin m)) \ positiveIndexSet q := by
  classical
  intro j hj
  rcases Finset.mem_image.mp hj with ⟨i, hi, rfl⟩
  have hqi : q i ≠ 0 :=
    (mem_positiveIndexSet q i).1 hi
  have hz : q (finRotate m i) = 0 :=
    hsep i hqi
  rw [Finset.mem_sdiff]
  constructor
  · simp
  · rw [mem_positiveIndexSet]
    exact not_ne_iff.mpr hz

/-- Independent-set bound on the cyclic support. -/
theorem positiveSupport_mul_two_le_length_of_cyclicSeparated
    {m : ℕ} (q : Fin m → ℕ)
    (hsep : CyclicSeparatedPositive q) :
    2 * positiveSupport q ≤ m := by
  classical
  let P := positiveIndexSet q
  let Z := (Finset.univ : Finset (Fin m)) \ P
  have himage :
      P.image (finRotate m) ⊆ Z := by
    simpa [P, Z] using
      rotate_positiveIndexSet_subset_zero q hsep
  have hcardImage :
      (P.image (finRotate m)).card = P.card :=
    Finset.card_image_of_injective P (finRotate m).injective
  have hPZ :
      P.card ≤ Z.card := by
    rw [← hcardImage]
    exact Finset.card_le_card himage
  have hZ :
      Z.card = m - P.card := by
    dsimp [Z]
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ P)]
    simp
  have hP :
      P.card = positiveSupport q := by
    simpa [P] using positiveIndexSet_card_eq_positiveSupport q
  rw [hZ, hP] at hPZ
  omega

/-- Equivalent half-length form. -/
theorem positiveSupport_le_half_length_of_cyclicSeparated
    {m : ℕ} (q : Fin m → ℕ)
    (hsep : CyclicSeparatedPositive q) :
    positiveSupport q ≤ m / 2 := by
  have h :=
    positiveSupport_mul_two_le_length_of_cyclicSeparated q hsep
  omega

/-- Stable cyclic separation plus the Sendov quotient-mass identity gives the
basic exponent/support accounting. -/
theorem floorExcess_add_support_le_of_cyclicSeparated
    {m n : ℕ} (q : Fin m → ℕ)
    (hQ : (∑ i, q i) ≤ n)
    (_hsep : CyclicSeparatedPositive q) :
    floorExcess q + positiveSupport q ≤ n := by
  rw [floorExcess_add_positiveSupport q]
  exact hQ

/-- In particular, any nonzero stable support consumes at least one unit of
the n-budget. -/
theorem floorExcess_lt_n_of_cyclicSeparated_nonempty
    {m n : ℕ} (q : Fin m → ℕ)
    (hQ : (∑ i, q i) ≤ n)
    (hsep : CyclicSeparatedPositive q)
    (hpos : 0 < positiveSupport q) :
    floorExcess q < n := by
  have h :=
    floorExcess_add_support_le_of_cyclicSeparated
      q hQ hsep
  omega

#print axioms positiveIndexSet_card_eq_positiveSupport
#print axioms positiveSupport_mul_two_le_length_of_cyclicSeparated
#print axioms positiveSupport_le_half_length_of_cyclicSeparated
#print axioms floorExcess_add_support_le_of_cyclicSeparated

end JSP000404Research
