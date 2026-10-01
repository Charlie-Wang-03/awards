import JSP000404Research.MinimalBlockDeficiency
import Mathlib.Tactic

/-!
# Connectivity of a minimal Hall-deficient block family

Attach a graph to a finite block family T by joining distinct vertices u,v
when their candidate blocks intersect.

An inclusion-minimal deficient set cannot split into two nonempty parts with no
cross-block intersection.  Indeed both proper parts satisfy Hall expansion by
minimality, their block unions are disjoint, and adding the two inequalities
gives expansion for T.

This file records the cut form needed later: every nontrivial partition of a
minimal deficient set has at least one shared candidate word crossing the cut.
Equivalently, the block-intersection graph is connected.
-/

namespace JSP000404Research

def BlocksCross
    {V W : Type*} [DecidableEq W]
    (blocks : V → Finset W)
    (u v : V) : Prop :=
  (blocks u ∩ blocks v).Nonempty

theorem biUnion_disjoint_of_no_cross
    {V W : Type*} [Fintype V] [DecidableEq V] [DecidableEq W]
    (blocks : V → Finset W)
    {A B : Finset V}
    (hcross :
      ∀ u ∈ A, ∀ v ∈ B,
        ¬ BlocksCross blocks u v) :
    Disjoint (A.biUnion blocks) (B.biUnion blocks) := by
  classical
  rw [Finset.disjoint_left]
  intro word hA hB
  obtain ⟨u,huA,huWord⟩ := Finset.mem_biUnion.mp hA
  obtain ⟨v,hvB,hvWord⟩ := Finset.mem_biUnion.mp hB
  exact hcross u huA v hvB
    ⟨word,huWord,hvWord⟩

theorem minimal_deficient_has_crossing_every_partition
    {V W : Type*} [Fintype V] [DecidableEq V] [DecidableEq W]
    (demand : V → ℕ)
    (blocks : V → Finset W)
    {T A B : Finset V}
    (hdef : BlockDeficient demand blocks T)
    (hmin :
      ∀ U : Finset V,
        U ⊂ T →
        ¬ BlockDeficient demand blocks U)
    (hunion : T = A ∪ B)
    (hAdisjB : Disjoint A B)
    (hA : A.Nonempty)
    (hB : B.Nonempty) :
    ∃ u ∈ A, ∃ v ∈ B,
      BlocksCross blocks u v := by
  classical
  by_contra hnone
  push_neg at hnone
  have hAproper : A ⊂ T := by
    constructor
    · rw [hunion]
      exact Finset.subset_union_left
    · intro hTA
      have hBsubA : B ⊆ A := by
        intro v hv
        have hvT : v ∈ T := by
          rw [hunion]
          exact Finset.mem_union_right A hv
        rw [← hTA] at hvT
        exact hvT
      obtain ⟨v,hvB⟩ := hB
      have hvA := hBsubA hvB
      exact Finset.disjoint_left.mp hAdisjB hvA hvB
  have hBproper : B ⊂ T := by
    constructor
    · rw [hunion]
      exact Finset.subset_union_right
    · intro hTB
      have hAsubB : A ⊆ B := by
        intro u hu
        have huT : u ∈ T := by
          rw [hunion]
          exact Finset.mem_union_left B hu
        rw [← hTB] at huT
        exact huT
      obtain ⟨u,huA⟩ := hA
      have huB := hAsubB huA
      exact Finset.disjoint_left.mp hAdisjB huA huB
  have hAexpand :
      (∑ u ∈ A, demand u) ≤
        (A.biUnion blocks).card := by
    have hnot := hmin A hAproper
    unfold BlockDeficient at hnot
    omega
  have hBexpand :
      (∑ v ∈ B, demand v) ≤
        (B.biUnion blocks).card := by
    have hnot := hmin B hBproper
    unfold BlockDeficient at hnot
    omega
  have hUnionDisj :
      Disjoint (A.biUnion blocks) (B.biUnion blocks) :=
    biUnion_disjoint_of_no_cross blocks hnone
  have hDemandSplit :
      (∑ x ∈ T, demand x) =
        (∑ u ∈ A, demand u) +
          (∑ v ∈ B, demand v) := by
    rw [hunion, Finset.sum_union hAdisjB]
  have hBlockSplit :
      (T.biUnion blocks).card =
        (A.biUnion blocks).card +
          (B.biUnion blocks).card := by
    rw [hunion, Finset.biUnion_union,
        Finset.card_union_of_disjoint hUnionDisj]
  unfold BlockDeficient at hdef
  rw [hDemandSplit,hBlockSplit] at hdef
  omega

#print axioms biUnion_disjoint_of_no_cross
#print axioms minimal_deficient_has_crossing_every_partition

end JSP000404Research
