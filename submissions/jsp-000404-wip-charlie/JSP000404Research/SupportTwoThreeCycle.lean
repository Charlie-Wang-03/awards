import JSP000404Research.SupportTwoDeletion
import Mathlib.Tactic

/-!
# Support two on a three-gap cycle

At a centre of a four-point configuration there are exactly three cyclic
projective gaps.  If exactly two quotient gaps are positive, then some cyclic
adjacent pair is positive.  Deleting their common ray merges that pair.

The linear SupportTwoDeletion theorem handles ordinary adjacent pairs.  This
file adds the three-cycle wrap pair explicitly and packages the exact
conclusion: among the three possible cyclic merges, at least one raises the
list exponent by one, independently of the nonnegative carry.

This is the finite local ingredient for the direct four-centre terminal.
-/

namespace JSP000404Research

/-- The three cyclic ray deletions, expressed only at quotient level. -/
def mergeThreeAB (a b c carry : ℕ) : List ℕ :=
  [a + b + carry, c]

def mergeThreeBC (a b c carry : ℕ) : List ℕ :=
  [a, b + c + carry]

def mergeThreeCA (a b c carry : ℕ) : List ℕ :=
  [a + c + carry, b]

@[simp] theorem listExponent_three
    (a b c : ℕ) :
    listExponent [a,b,c] =
      excess a + excess b + excess c := by
  simp [listExponent, add_assoc, add_left_comm, add_comm]

@[simp] theorem listExponent_mergeThreeAB
    (a b c carry : ℕ) :
    listExponent (mergeThreeAB a b c carry) =
      excess (a + b + carry) + excess c := by
  simp [mergeThreeAB, listExponent]

@[simp] theorem listExponent_mergeThreeBC
    (a b c carry : ℕ) :
    listExponent (mergeThreeBC a b c carry) =
      excess a + excess (b + c + carry) := by
  simp [mergeThreeBC, listExponent]

@[simp] theorem listExponent_mergeThreeCA
    (a b c carry : ℕ) :
    listExponent (mergeThreeCA a b c carry) =
      excess (a + c + carry) + excess b := by
  simp [mergeThreeCA, listExponent]

/-- Exactly two positive entries among three force one of the three cyclic
adjacent pairs to be positive. -/
theorem three_support_two_has_positive_cyclic_pair
    {a b c : ℕ}
    (hsupport : listPositiveCount [a,b,c] = 2) :
    (1 ≤ a ∧ 1 ≤ b) ∨
      (1 ≤ b ∧ 1 ≤ c) ∨
      (1 ≤ c ∧ 1 ≤ a) := by
  by_cases ha : a = 0 <;>
    by_cases hb : b = 0 <;>
    by_cases hc : c = 0 <;>
    simp [listPositiveCount, ha, hb, hc] at hsupport ⊢ <;>
    omega

/-- A support-two three-cycle has a deletion merge which raises the exponent
by at least one for every carry value. -/
theorem three_support_two_exists_cyclic_gain
    {a b c : ℕ}
    (hsupport : listPositiveCount [a,b,c] = 2) :
    (
      (1 ≤ a ∧ 1 ≤ b) ∧
        ∀ carry,
          listExponent [a,b,c] + 1 ≤
            listExponent (mergeThreeAB a b c carry)
    ) ∨
    (
      (1 ≤ b ∧ 1 ≤ c) ∧
        ∀ carry,
          listExponent [a,b,c] + 1 ≤
            listExponent (mergeThreeBC a b c carry)
    ) ∨
    (
      (1 ≤ c ∧ 1 ≤ a) ∧
        ∀ carry,
          listExponent [a,b,c] + 1 ≤
            listExponent (mergeThreeCA a b c carry)
    ) := by
  rcases three_support_two_has_positive_cyclic_pair hsupport with hab | hbc | hca
  · left
    refine ⟨hab, ?_⟩
    intro carry
    have hlocal :=
      excess_merge_gain_of_both_pos
        (a := a) (b := b) (c := carry) hab.1 hab.2
    simp only [listExponent_three, listExponent_mergeThreeAB]
    omega
  · rcases hbc with hbc | hca
    · right; left
      refine ⟨hbc, ?_⟩
      intro carry
      have hlocal :=
        excess_merge_gain_of_both_pos
          (a := b) (b := c) (c := carry) hbc.1 hbc.2
      simp only [listExponent_three, listExponent_mergeThreeBC]
      omega
    · right; right
      refine ⟨hca, ?_⟩
      intro carry
      have hlocal :=
        excess_merge_gain_of_both_pos
          (a := c) (b := a) (c := carry) hca.1 hca.2
      simp only [listExponent_three, listExponent_mergeThreeCA]
      omega

/-- Dyadic form: one of the three cyclic deletions at least doubles this
centre's old weight. -/
theorem three_support_two_exists_cyclic_doubling
    {a b c : ℕ}
    (hsupport : listPositiveCount [a,b,c] = 2) :
    (
      ∀ carry,
        2 * 2 ^ listExponent [a,b,c] ≤
          2 ^ listExponent (mergeThreeAB a b c carry)
    ) ∨
    (
      ∀ carry,
        2 * 2 ^ listExponent [a,b,c] ≤
          2 ^ listExponent (mergeThreeBC a b c carry)
    ) ∨
    (
      ∀ carry,
        2 * 2 ^ listExponent [a,b,c] ≤
          2 ^ listExponent (mergeThreeCA a b c carry)
    ) := by
  rcases three_support_two_exists_cyclic_gain hsupport with h | h | h
  · left
    intro carry
    have hp :=
      Nat.pow_le_pow_right (by norm_num : 0 < 2) (h.2 carry)
    rw [pow_succ] at hp
    simpa [Nat.mul_comm] using hp
  · right; left
    intro carry
    have hp :=
      Nat.pow_le_pow_right (by norm_num : 0 < 2) (h.2 carry)
    rw [pow_succ] at hp
    simpa [Nat.mul_comm] using hp
  · right; right
    intro carry
    have hp :=
      Nat.pow_le_pow_right (by norm_num : 0 < 2) (h.2 carry)
    rw [pow_succ] at hp
    simpa [Nat.mul_comm] using hp

#print axioms three_support_two_has_positive_cyclic_pair
#print axioms three_support_two_exists_cyclic_gain
#print axioms three_support_two_exists_cyclic_doubling

end JSP000404Research
