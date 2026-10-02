import JSP000404Research.BoolSignPath
import Mathlib.Tactic

/-!
# Ordered alternating subsequences force two Boolean transitions

Two independent list facts used by the three-band terminal:

1. In a list pairwise sorted by a real-valued key, three members with strictly
   increasing keys occur in that same order.
2. A Boolean list containing b, !b, b in that order has at least two adjacent
   sign transitions.

The second statement is phrased using the transition count already used by the
projective sign-path machinery.
-/

namespace JSP000404Research

def boolListTransitionCount : List Bool → ℕ
  | [] => 0
  | a :: xs => boolTransitionCountFrom a xs

theorem boolListTransitionCount_tail_le
    (a : Bool) (xs : List Bool) :
    boolListTransitionCount xs ≤
      boolListTransitionCount (a :: xs) := by
  cases xs with
  | nil =>
      simp [boolListTransitionCount,boolTransitionCountFrom]
  | cons b bs =>
      simp only [boolListTransitionCount,boolTransitionCountFrom]
      split_ifs <;> omega

theorem boolListTransitionCount_suffix_le
    (pre xs : List Bool) :
    boolListTransitionCount xs ≤
      boolListTransitionCount (pre ++ xs) := by
  induction pre with
  | nil => simp
  | cons a pre ih =>
      simp only [List.cons_append]
      exact ih.trans
        (boolListTransitionCount_tail_le a (pre ++ xs))

theorem boolTransitionCountFrom_append
    (a : Bool) (xs ys : List Bool) :
    boolTransitionCountFrom a (xs ++ ys) =
      boolTransitionCountFrom a xs +
        boolTransitionCountFrom (boolLastFrom a xs) ys := by
  induction xs generalizing a with
  | nil =>
      simp [boolTransitionCountFrom,boolLastFrom]
  | cons b bs ih =>
      simp only [List.cons_append,boolTransitionCountFrom,boolLastFrom]
      rw [ih b]
      omega

theorem boolLastFrom_append
    (a : Bool) (xs ys : List Bool) :
    boolLastFrom a (xs ++ ys) =
      boolLastFrom (boolLastFrom a xs) ys := by
  induction xs generalizing a with
  | nil => simp [boolLastFrom]
  | cons b bs ih =>
      simp only [List.cons_append,boolLastFrom]
      exact ih b

theorem boolLastFrom_append_singleton
    (a b : Bool) (xs : List Bool) :
    boolLastFrom a (xs ++ [b]) = b := by
  rw [boolLastFrom_append]
  simp [boolLastFrom]

theorem one_le_transitionCount_to_opposite
    (a : Bool) (xs : List Bool)
    (hlast : boolLastFrom a xs = !a) :
    1 ≤ boolTransitionCountFrom a xs := by
  have hmod :=
    boolTransitionCountFrom_mod_two_eq_one_of_last_not
      a xs hlast
  omega

theorem alternating_three_bool_list_transitionCount_ge_two
    (b : Bool)
    (X Y Z W : List Bool) :
    2 ≤
      boolListTransitionCount
        (X ++ b :: Y ++ (!b) :: Z ++ b :: W) := by
  have hsuffix :
      boolListTransitionCount
          (b :: Y ++ (!b) :: Z ++ b :: W)
        ≤
      boolListTransitionCount
          (X ++ b :: Y ++ (!b) :: Z ++ b :: W) :=
    boolListTransitionCount_suffix_le
      X (b :: Y ++ (!b) :: Z ++ b :: W)

  have hseg1Last :
      boolLastFrom b (Y ++ [!b]) = !b :=
    boolLastFrom_append_singleton b (!b) Y
  have hseg1 :
      1 ≤ boolTransitionCountFrom b (Y ++ [!b]) :=
    one_le_transitionCount_to_opposite b
      (Y ++ [!b]) hseg1Last

  have hseg2Last :
      boolLastFrom (!b) (Z ++ [b]) = b := by
    have h :=
      boolLastFrom_append_singleton (!b) b Z
    simpa using h
  have hseg2 :
      1 ≤ boolTransitionCountFrom (!b) (Z ++ [b]) := by
    have hnotnot : !(!b) = b := by cases b <;> rfl
    apply one_le_transitionCount_to_opposite (!b)
    simpa [hnotnot] using hseg2Last

  have hcore :
      2 ≤
        boolListTransitionCount
          (b :: Y ++ (!b) :: Z ++ b :: W) := by
    unfold boolListTransitionCount
    have hsplit1 :=
      boolTransitionCountFrom_append
        b (Y ++ [!b]) (Z ++ b :: W)
    have hlast1 :
        boolLastFrom b (Y ++ [!b]) = !b :=
      hseg1Last
    rw [hlast1] at hsplit1
    have hsplit2 :=
      boolTransitionCountFrom_append
        (!b) (Z ++ [b]) W
    have hlast2 :
        boolLastFrom (!b) (Z ++ [b]) = b := by
      exact hseg2Last
    rw [hlast2] at hsplit2
    have hrewrite :
        Y ++ (!b) :: Z ++ b :: W =
          (Y ++ [!b]) ++ (Z ++ [b]) ++ W := by
      simp [List.append_assoc]
    rw [hrewrite, boolTransitionCountFrom_append]
    rw [hseg1Last]
    rw [boolTransitionCountFrom_append]
    omega
  exact hcore.trans hsuffix

theorem sorted_three_members_decompose
    {α : Type*}
    (f : α → ℝ)
    (l : List α)
    {a b c : α}
    (hsorted : l.Pairwise (fun x y => f x ≤ f y))
    (ha : a ∈ l) (hb : b ∈ l) (hc : c ∈ l)
    (hab : f a < f b)
    (hbc : f b < f c) :
    ∃ X Y Z W : List α,
      l = X ++ a :: Y ++ b :: Z ++ c :: W := by
  obtain ⟨X,tailA,hA⟩ :=
    exists_append_cons_of_mem ha
  have hbTail : b ∈ tailA := by
    rw [hA] at hb hsorted
    simp only [List.mem_append,List.mem_cons] at hb
    rcases hb with hbX | hba | hbTail
    · have hp := List.pairwise_append.mp hsorted
      have hle :=
        hp.2.2 b hbX a (by simp)
      linarith
    · subst b
      linarith
    · exact hbTail
  have hcTailA : c ∈ tailA := by
    rw [hA] at hc hsorted
    simp only [List.mem_append,List.mem_cons] at hc
    rcases hc with hcX | hca | hcTail
    · have hp := List.pairwise_append.mp hsorted
      have hle :=
        hp.2.2 c hcX a (by simp)
      linarith
    · subst c
      linarith
    · exact hcTail
  obtain ⟨Y,tailB,hB⟩ :=
    exists_append_cons_of_mem hbTail
  have hcTail : c ∈ tailB := by
    rw [hB] at hcTailA
    have hsortedTailA : tailA.Pairwise (fun x y => f x ≤ f y) := by
      rw [hA] at hsorted
      exact (List.pairwise_append.mp hsorted).2.1
    rw [hB] at hsortedTailA
    simp only [List.mem_append,List.mem_cons] at hcTailA
    rcases hcTailA with hcY | hcb | hcTail
    · have hp := List.pairwise_append.mp hsortedTailA
      have hle :=
        hp.2.2 c hcY b (by simp)
      linarith
    · subst c
      linarith
    · exact hcTail
  obtain ⟨Z,W,hC⟩ :=
    exists_append_cons_of_mem hcTail
  refine ⟨X,Y,Z,W,?_⟩
  rw [hA,hB,hC]
  simp [List.append_assoc]

#print axioms alternating_three_bool_list_transitionCount_ge_two
#print axioms sorted_three_members_decompose

end JSP000404Research
