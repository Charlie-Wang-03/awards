
import JSP000404Research.TwoStepMergeRigidity
import JSP000404Research.PinnedCyclicDeletionGain
import Mathlib.Tactic

/-!
# Two adjacent zero-gain merges on an explicit quotient list

Write three consecutive old quotient gaps as a,b,c.

The parent, first child, and second child quotient lists are

  prefix ++ [a,b,c] ++ suffix
  prefix ++ [a+b+carry1,c] ++ suffix
  prefix ++ [a+b+carry1+c+carry2] ++ suffix.

If listExponent is unchanged at both steps, then the local arithmetic
TwoStepMergeRigidity applies: at most one of a,b,c is positive.

This is the list-shaped bridge needed before instantiating the result with
actual adjacent ray deletions.
-/

namespace JSP000404Research

def adjacentDoubleMergeParent
    (prefix : List ℕ) (a b c : ℕ)
    (suffix : List ℕ) : List ℕ :=
  prefix ++ [a,b,c] ++ suffix

def adjacentDoubleMergeChild₁
    (prefix : List ℕ) (a b c carry₁ : ℕ)
    (suffix : List ℕ) : List ℕ :=
  prefix ++ [a + b + carry₁, c] ++ suffix

def adjacentDoubleMergeChild₂
    (prefix : List ℕ) (a b c carry₁ carry₂ : ℕ)
    (suffix : List ℕ) : List ℕ :=
  prefix ++ [a + b + carry₁ + c + carry₂] ++ suffix

theorem listExponent_adjacentDoubleMerge_parent
    (prefix suffix : List ℕ)
    (a b c : ℕ) :
    listExponent
        (adjacentDoubleMergeParent prefix a b c suffix)
      =
    listExponent prefix +
      excess a + excess b + excess c +
      listExponent suffix := by
  simp [adjacentDoubleMergeParent, listExponent,
    List.map_append, add_assoc]

theorem listExponent_adjacentDoubleMerge_child₁
    (prefix suffix : List ℕ)
    (a b c carry₁ : ℕ) :
    listExponent
        (adjacentDoubleMergeChild₁
          prefix a b c carry₁ suffix)
      =
    listExponent prefix +
      excess (a + b + carry₁) + excess c +
      listExponent suffix := by
  simp [adjacentDoubleMergeChild₁, listExponent,
    List.map_append, add_assoc]

theorem listExponent_adjacentDoubleMerge_child₂
    (prefix suffix : List ℕ)
    (a b c carry₁ carry₂ : ℕ) :
    listExponent
        (adjacentDoubleMergeChild₂
          prefix a b c carry₁ carry₂ suffix)
      =
    listExponent prefix +
      excess (a + b + carry₁ + c + carry₂) +
      listExponent suffix := by
  simp [adjacentDoubleMergeChild₂, listExponent,
    List.map_append, add_assoc]

/-- First displayed equality is exactly a zero-gain merge of a,b. -/
theorem first_zero_gain_of_adjacentDoubleMerge_exponent_eq
    (prefix suffix : List ℕ)
    (a b c carry₁ : ℕ)
    (h :
      listExponent
          (adjacentDoubleMergeChild₁
            prefix a b c carry₁ suffix)
        =
      listExponent
          (adjacentDoubleMergeParent
            prefix a b c suffix)) :
    exponentAfterMerge
        (listExponent prefix + excess c +
          listExponent suffix)
        a b carry₁
      =
    exponentBeforeMerge
        (listExponent prefix + excess c +
          listExponent suffix)
        a b := by
  rw [listExponent_adjacentDoubleMerge_child₁,
      listExponent_adjacentDoubleMerge_parent] at h
  unfold exponentAfterMerge exponentBeforeMerge
  omega

/-- Second displayed equality is exactly a zero-gain merge of the first
merged quotient with c. -/
theorem second_zero_gain_of_adjacentDoubleMerge_exponent_eq
    (prefix suffix : List ℕ)
    (a b c carry₁ carry₂ : ℕ)
    (h :
      listExponent
          (adjacentDoubleMergeChild₂
            prefix a b c carry₁ carry₂ suffix)
        =
      listExponent
          (adjacentDoubleMergeChild₁
            prefix a b c carry₁ suffix)) :
    exponentAfterMerge
        (listExponent prefix + listExponent suffix)
        (a + b + carry₁) c carry₂
      =
    exponentBeforeMerge
        (listExponent prefix + listExponent suffix)
        (a + b + carry₁) c := by
  rw [listExponent_adjacentDoubleMerge_child₂,
      listExponent_adjacentDoubleMerge_child₁] at h
  unfold exponentAfterMerge exponentBeforeMerge
  omega

/-- Main explicit-list two-step rigidity theorem. -/
theorem adjacentDoubleMerge_triple_shape_of_two_exponent_equalities
    (prefix suffix : List ℕ)
    (a b c carry₁ carry₂ : ℕ)
    (h₁ :
      listExponent
          (adjacentDoubleMergeChild₁
            prefix a b c carry₁ suffix)
        =
      listExponent
          (adjacentDoubleMergeParent
            prefix a b c suffix))
    (h₂ :
      listExponent
          (adjacentDoubleMergeChild₂
            prefix a b c carry₁ carry₂ suffix)
        =
      listExponent
          (adjacentDoubleMergeChild₁
            prefix a b c carry₁ suffix)) :
    (a = 0 ∧ b = 0) ∨
    (a = 0 ∧ c = 0) ∨
    (b = 0 ∧ c = 0) := by
  exact two_step_zero_gain_triple_shape
    (first_zero_gain_of_adjacentDoubleMerge_exponent_eq
      prefix suffix a b c carry₁ h₁)
    (second_zero_gain_of_adjacentDoubleMerge_exponent_eq
      prefix suffix a b c carry₁ carry₂ h₂)

/-- Equivalent pairwise-positive exclusion form. -/
theorem adjacentDoubleMerge_triple_pairwise_sparse_of_two_exponent_equalities
    (prefix suffix : List ℕ)
    (a b c carry₁ carry₂ : ℕ)
    (h₁ :
      listExponent
          (adjacentDoubleMergeChild₁
            prefix a b c carry₁ suffix)
        =
      listExponent
          (adjacentDoubleMergeParent
            prefix a b c suffix))
    (h₂ :
      listExponent
          (adjacentDoubleMergeChild₂
            prefix a b c carry₁ carry₂ suffix)
        =
      listExponent
          (adjacentDoubleMergeChild₁
            prefix a b c carry₁ suffix)) :
    ¬ (1 ≤ a ∧ 1 ≤ b) ∧
    ¬ (1 ≤ a ∧ 1 ≤ c) ∧
    ¬ (1 ≤ b ∧ 1 ≤ c) := by
  exact two_step_zero_gain_triple_pairwise_sparse
    (first_zero_gain_of_adjacentDoubleMerge_exponent_eq
      prefix suffix a b c carry₁ h₁)
    (second_zero_gain_of_adjacentDoubleMerge_exponent_eq
      prefix suffix a b c carry₁ carry₂ h₂)

#print axioms adjacentDoubleMerge_triple_shape_of_two_exponent_equalities
#print axioms adjacentDoubleMerge_triple_pairwise_sparse_of_two_exponent_equalities

end JSP000404Research
