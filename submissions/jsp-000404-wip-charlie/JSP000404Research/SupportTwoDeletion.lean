import JSP000404Research.MergeGain
import Mathlib.Tactic

/-!
# Support-two centres and adjacent-positive deletion gain

For a quotient list, define its Sendov exponent as the sum of
  excess(q) = (q-1)_+
over all entries.

If two adjacent quotient entries a,b are both positive, deleting their common
ray merges them to a+b+carry.  The local MergeGain theorem already says this
raises the two-entry exponent contribution by at least one.  This file lifts
that fact to the full quotient list and then to dyadic weight.

Consequently, a support-two centre can be stable under every deletion only if
its two positive quotient gaps are not adjacent in the cyclic gap order.
The remaining separated support-two regime is therefore the genuine global
difficulty.
-/

namespace JSP000404Research

/-- Sendov exponent of a quotient list. -/
def listExponent (qs : List ℕ) : ℕ :=
  (qs.map excess).sum

/-- Merge one displayed adjacent pair in a quotient list. -/
def mergeDisplayedAdjacent
    (pre : List ℕ) (a b carry : ℕ) (post : List ℕ) : List ℕ :=
  pre ++ (a + b + carry) :: post

/-- Exact decomposition of list exponent across a displayed adjacent pair. -/
theorem listExponent_displayed_pair
    (pre post : List ℕ) (a b : ℕ) :
    listExponent (pre ++ a :: b :: post) =
      listExponent pre + excess a + excess b + listExponent post := by
  simp [listExponent, List.map_append, add_assoc, add_left_comm, add_comm]

/-- Exponent after the displayed merge. -/
theorem listExponent_merged_displayed_pair
    (pre post : List ℕ) (a b carry : ℕ) :
    listExponent (mergeDisplayedAdjacent pre a b carry post) =
      listExponent pre + excess (a + b + carry) + listExponent post := by
  simp [mergeDisplayedAdjacent, listExponent,
    List.map_append, add_assoc, add_left_comm, add_comm]

/-- Two adjacent positive quotient gaps guarantee at least one exponent unit
of deletion gain, independently of the carry. -/
theorem listExponent_merge_gain_of_adjacent_positive
    (pre post : List ℕ) {a b carry : ℕ}
    (ha : 1 ≤ a) (hb : 1 ≤ b) :
    listExponent (pre ++ a :: b :: post) + 1 ≤
      listExponent (mergeDisplayedAdjacent pre a b carry post) := by
  rw [listExponent_displayed_pair,
      listExponent_merged_displayed_pair]
  have hlocal :=
    excess_merge_gain_of_both_pos
      (a := a) (b := b) (c := carry) ha hb
  omega

/-- Hence the merged dyadic weight is at least twice the old weight. -/
theorem dyadic_weight_doubles_of_adjacent_positive_merge
    (pre post : List ℕ) {a b carry : ℕ}
    (ha : 1 ≤ a) (hb : 1 ≤ b) :
    2 * 2 ^ listExponent (pre ++ a :: b :: post) ≤
      2 ^ listExponent
        (mergeDisplayedAdjacent pre a b carry post) := by
  have hgain :=
    listExponent_merge_gain_of_adjacent_positive
      pre post (carry := carry) ha hb
  have hpow :=
    Nat.pow_le_pow_right (by norm_num : 0 < 2) hgain
  rw [pow_succ] at hpow
  simpa [Nat.mul_comm] using hpow

/-- A linear quotient list contains an adjacent positive pair. -/
def HasAdjacentPositive (qs : List ℕ) : Prop :=
  ∃ pre post : List ℕ, ∃ a b : ℕ,
    qs = pre ++ a :: b :: post ∧
    1 ≤ a ∧ 1 ≤ b

/-- If a support-two list has an adjacent positive pair, that displayed pair
is a deletion-gain witness. -/
theorem exists_gain_merge_of_support_two_and_adjacent
    (qs : List ℕ)
    (hsupport : listPositiveCount qs = 2)
    (hadj : HasAdjacentPositive qs) :
    ∃ pre post : List ℕ, ∃ a b : ℕ,
      qs = pre ++ a :: b :: post ∧
      1 ≤ a ∧ 1 ≤ b ∧
      ∀ carry : ℕ,
        listExponent qs + 1 ≤
          listExponent
            (mergeDisplayedAdjacent pre a b carry post) := by
  rcases hadj with ⟨pre, post, a, b, hq, ha, hb⟩
  refine ⟨pre, post, a, b, hq, ha, hb, ?_⟩
  intro carry
  rw [hq]
  exact listExponent_merge_gain_of_adjacent_positive
    pre post ha hb

/-- In particular, if every displayed adjacent merge is exponent-neutral,
there cannot be a pair of adjacent positive quotient entries. -/
theorem no_adjacent_positive_of_all_merges_neutral
    (qs : List ℕ)
    (hneutral :
      ∀ pre post : List ℕ, ∀ a b : ℕ,
        qs = pre ++ a :: b :: post →
        ∀ carry : ℕ,
          listExponent
              (mergeDisplayedAdjacent pre a b carry post)
            =
          listExponent qs) :
    ¬ HasAdjacentPositive qs := by
  intro hadj
  rcases hadj with ⟨pre, post, a, b, hq, ha, hb⟩
  have hgain :=
    listExponent_merge_gain_of_adjacent_positive
      pre post (carry := 0) ha hb
  have hzero :=
    hneutral pre post a b hq 0
  rw [hzero] at hgain
  omega

#print axioms listExponent_merge_gain_of_adjacent_positive
#print axioms dyadic_weight_doubles_of_adjacent_positive_merge
#print axioms exists_gain_merge_of_support_two_and_adjacent
#print axioms no_adjacent_positive_of_all_merges_neutral

end JSP000404Research
