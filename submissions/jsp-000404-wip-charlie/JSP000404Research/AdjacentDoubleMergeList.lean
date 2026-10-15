
import JSP000404Research.TwoStepMergeRigidity
import JSP000404Research.PinnedCyclicDeletionGain
import Mathlib.Tactic

/-!
# Two adjacent zero-gain merges on an explicit quotient list

Write three consecutive old quotient gaps as a,b,c.

The parent, first child, and second child quotient lists are

  pre ++ [a,b,c] ++ suffix
  pre ++ [a+b+carry1,c] ++ suffix
  pre ++ [a+b+carry1+c+carry2] ++ suffix.

If listExponent is unchanged at both steps, then the local arithmetic
TwoStepMergeRigidity applies: at most one of a,b,c is positive.

This is the list-shaped bridge needed before instantiating the result with
actual adjacent ray deletions.
-/

namespace JSP000404Research

def adjacentDoubleMergeParent
    (pre : List ℕ) (a b c : ℕ)
    (suffix : List ℕ) : List ℕ :=
  pre ++ [a,b,c] ++ suffix

def adjacentDoubleMergeChild₁
    (pre : List ℕ) (a b c carry₁ : ℕ)
    (suffix : List ℕ) : List ℕ :=
  pre ++ [a + b + carry₁, c] ++ suffix

def adjacentDoubleMergeChild₂
    (pre : List ℕ) (a b c carry₁ carry₂ : ℕ)
    (suffix : List ℕ) : List ℕ :=
  pre ++ [a + b + carry₁ + c + carry₂] ++ suffix

theorem listExponent_adjacentDoubleMerge_parent
    (pre suffix : List ℕ)
    (a b c : ℕ) :
    listExponent
        (adjacentDoubleMergeParent pre a b c suffix)
      =
    listExponent pre +
      excess a + excess b + excess c +
      listExponent suffix := by
  simp [adjacentDoubleMergeParent, listExponent,
    List.map_append, add_assoc]

theorem listExponent_adjacentDoubleMerge_child₁
    (pre suffix : List ℕ)
    (a b c carry₁ : ℕ) :
    listExponent
        (adjacentDoubleMergeChild₁
          pre a b c carry₁ suffix)
      =
    listExponent pre +
      excess (a + b + carry₁) + excess c +
      listExponent suffix := by
  simp [adjacentDoubleMergeChild₁, listExponent,
    List.map_append, add_assoc]

theorem listExponent_adjacentDoubleMerge_child₂
    (pre suffix : List ℕ)
    (a b c carry₁ carry₂ : ℕ) :
    listExponent
        (adjacentDoubleMergeChild₂
          pre a b c carry₁ carry₂ suffix)
      =
    listExponent pre +
      excess (a + b + carry₁ + c + carry₂) +
      listExponent suffix := by
  simp [adjacentDoubleMergeChild₂, listExponent,
    List.map_append, add_assoc]

/-- First displayed equality is exactly a zero-gain merge of a,b. -/
theorem first_zero_gain_of_adjacentDoubleMerge_exponent_eq
    (pre suffix : List ℕ)
    (a b c carry₁ : ℕ)
    (h :
      listExponent
          (adjacentDoubleMergeChild₁
            pre a b c carry₁ suffix)
        =
      listExponent
          (adjacentDoubleMergeParent
            pre a b c suffix)) :
    exponentAfterMerge
        (listExponent pre + excess c +
          listExponent suffix)
        a b carry₁
      =
    exponentBeforeMerge
        (listExponent pre + excess c +
          listExponent suffix)
        a b := by
  rw [listExponent_adjacentDoubleMerge_child₁,
      listExponent_adjacentDoubleMerge_parent] at h
  unfold exponentAfterMerge exponentBeforeMerge
  omega

/-- Second displayed equality is exactly a zero-gain merge of the first
merged quotient with c. -/
theorem second_zero_gain_of_adjacentDoubleMerge_exponent_eq
    (pre suffix : List ℕ)
    (a b c carry₁ carry₂ : ℕ)
    (h :
      listExponent
          (adjacentDoubleMergeChild₂
            pre a b c carry₁ carry₂ suffix)
        =
      listExponent
          (adjacentDoubleMergeChild₁
            pre a b c carry₁ suffix)) :
    exponentAfterMerge
        (listExponent pre + listExponent suffix)
        (a + b + carry₁) c carry₂
      =
    exponentBeforeMerge
        (listExponent pre + listExponent suffix)
        (a + b + carry₁) c := by
  rw [listExponent_adjacentDoubleMerge_child₂,
      listExponent_adjacentDoubleMerge_child₁] at h
  unfold exponentAfterMerge exponentBeforeMerge
  omega

/-- Main explicit-list two-step rigidity theorem. -/
theorem adjacentDoubleMerge_triple_shape_of_two_exponent_equalities
    (pre suffix : List ℕ)
    (a b c carry₁ carry₂ : ℕ)
    (h₁ :
      listExponent
          (adjacentDoubleMergeChild₁
            pre a b c carry₁ suffix)
        =
      listExponent
          (adjacentDoubleMergeParent
            pre a b c suffix))
    (h₂ :
      listExponent
          (adjacentDoubleMergeChild₂
            pre a b c carry₁ carry₂ suffix)
        =
      listExponent
          (adjacentDoubleMergeChild₁
            pre a b c carry₁ suffix)) :
    (a = 0 ∧ b = 0) ∨
    (a = 0 ∧ c = 0) ∨
    (b = 0 ∧ c = 0) := by
  exact two_step_zero_gain_triple_shape
    (first_zero_gain_of_adjacentDoubleMerge_exponent_eq
      pre suffix a b c carry₁ h₁)
    (second_zero_gain_of_adjacentDoubleMerge_exponent_eq
      pre suffix a b c carry₁ carry₂ h₂)

/-- Equivalent pairwise-positive exclusion form. -/
theorem adjacentDoubleMerge_triple_pairwise_sparse_of_two_exponent_equalities
    (pre suffix : List ℕ)
    (a b c carry₁ carry₂ : ℕ)
    (h₁ :
      listExponent
          (adjacentDoubleMergeChild₁
            pre a b c carry₁ suffix)
        =
      listExponent
          (adjacentDoubleMergeParent
            pre a b c suffix))
    (h₂ :
      listExponent
          (adjacentDoubleMergeChild₂
            pre a b c carry₁ carry₂ suffix)
        =
      listExponent
          (adjacentDoubleMergeChild₁
            pre a b c carry₁ suffix)) :
    ¬ (1 ≤ a ∧ 1 ≤ b) ∧
    ¬ (1 ≤ a ∧ 1 ≤ c) ∧
    ¬ (1 ≤ b ∧ 1 ≤ c) := by
  exact two_step_zero_gain_triple_pairwise_sparse
    (first_zero_gain_of_adjacentDoubleMerge_exponent_eq
      pre suffix a b c carry₁ h₁)
    (second_zero_gain_of_adjacentDoubleMerge_exponent_eq
      pre suffix a b c carry₁ carry₂ h₂)

#print axioms adjacentDoubleMerge_triple_shape_of_two_exponent_equalities
#print axioms adjacentDoubleMerge_triple_pairwise_sparse_of_two_exponent_equalities

end JSP000404Research
