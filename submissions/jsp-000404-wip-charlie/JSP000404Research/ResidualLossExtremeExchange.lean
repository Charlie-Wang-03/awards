import JSP000404Research.ResidualLossTranslatedConflict
import JSP000404Research.ResidualLocalCandidateCapacity
import Mathlib.Tactic

/-!
# Two-loss exchange along one common retained coordinate

Let u and v be distinct projected-loss vertices and let c be retained-active at
both.  Translate both loss cubes by the same Boolean involution flip_c.

The two original cubes are disjoint, and the two translated cubes are also
disjoint.  The only possible internal overlaps of the two doubled blocks are
the cross terms

  flip_c(Q_u) ∩ Q_v
  Q_u ∩ flip_c(Q_v).

The involution flip_c gives a bijection between these two cross terms, so they
have equal cardinality.

This is the exact exchange structure of the global-bottom/global-top loss pair
when c is their connecting retained edge colour.
-/

namespace JSP000404Research
namespace OrderedEdgeColoring

theorem loss_original_cubes_disjoint
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexp : ∀ v, exponent v ≤ n)
    (honeLoss :
      ∀ v, (active C v).card ≤ n - exponent v + 1)
    {u v : V}
    (huLoss : u ∈ projectedLossVertices C exponent)
    (huv : u ≠ v) :
    Disjoint
      (retainedCompletionWords C u)
      (retainedCompletionWords C v) :=
  projectedLoss_completion_disjoint
    C exponent hexp honeLoss huLoss huv

theorem flip_maps_translated_original_cross
    {V : Type*} [LinearOrder V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (u v : V) (c : Fin n)
    {word : Fin n → Bool}
    (hword :
      word ∈ translatedCompletionWords C u c ∩
        retainedCompletionWords C v) :
    flipBoolWordAt word c ∈
      retainedCompletionWords C u ∩
        translatedCompletionWords C v c := by
  have hparts := Finset.mem_inter.mp hword
  apply Finset.mem_inter.mpr
  constructor
  · exact (mem_translatedCompletionWords C u c word).1 hparts.1
  · apply (mem_translatedCompletionWords
      C v c (flipBoolWordAt word c)).2
    simpa [flipBoolWordAt_involutive] using hparts.2

theorem flip_maps_original_translated_cross
    {V : Type*} [LinearOrder V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (u v : V) (c : Fin n)
    {word : Fin n → Bool}
    (hword :
      word ∈ retainedCompletionWords C u ∩
        translatedCompletionWords C v c) :
    flipBoolWordAt word c ∈
      translatedCompletionWords C u c ∩
        retainedCompletionWords C v := by
  have hparts := Finset.mem_inter.mp hword
  apply Finset.mem_inter.mpr
  constructor
  · apply (mem_translatedCompletionWords
      C u c (flipBoolWordAt word c)).2
    simpa [flipBoolWordAt_involutive] using hparts.1
  · exact (mem_translatedCompletionWords C v c word).1 hparts.2

theorem loss_cross_exchange_card_eq
    {V : Type*} [LinearOrder V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (u v : V) (c : Fin n) :
    (translatedCompletionWords C u c ∩
        retainedCompletionWords C v).card
      =
    (retainedCompletionWords C u ∩
        translatedCompletionWords C v c).card := by
  classical
  let A :=
    translatedCompletionWords C u c ∩
      retainedCompletionWords C v
  let B :=
    retainedCompletionWords C u ∩
      translatedCompletionWords C v c
  have hf :
      Set.MapsTo
        (fun word => flipBoolWordAt word c)
        (A : Set (Fin n → Bool))
        (B : Set (Fin n → Bool)) := by
    intro word hword
    exact flip_maps_translated_original_cross
      C u v c hword
  have hg :
      Set.MapsTo
        (fun word => flipBoolWordAt word c)
        (B : Set (Fin n → Bool))
        (A : Set (Fin n → Bool)) := by
    intro word hword
    exact flip_maps_original_translated_cross
      C u v c hword
  have hinj :
      Set.InjOn
        (fun word => flipBoolWordAt word c)
        (A : Set (Fin n → Bool)) := by
    intro x hx y hy hxy
    exact flipBoolWordAt_injective c hxy
  have hinj' :
      Set.InjOn
        (fun word => flipBoolWordAt word c)
        (B : Set (Fin n → Bool)) := by
    intro x hx y hy hxy
    exact flipBoolWordAt_injective c hxy
  have hAB : A.card ≤ B.card :=
    Finset.card_le_card_of_injOn
      (fun word => flipBoolWordAt word c) hf hinj
  have hBA : B.card ≤ A.card :=
    Finset.card_le_card_of_injOn
      (fun word => flipBoolWordAt word c) hg hinj'
  exact Nat.le_antisymm hAB hBA

theorem same_coordinate_loss_doubled_union_card
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexp : ∀ v, exponent v ≤ n)
    (honeLoss :
      ∀ v, (active C v).card ≤ n - exponent v + 1)
    {u v : V}
    (huLoss : u ∈ projectedLossVertices C exponent)
    (hvLoss : v ∈ projectedLossVertices C exponent)
    (huv : u ≠ v)
    {c : Fin n}
    (hcu : c ∈ retainedActive C u)
    (hcv : c ∈ retainedActive C v) :
    (doubledCompletionBlock C u c ∪
      doubledCompletionBlock C v c).card
      =
    2 ^ exponent u + 2 ^ exponent v -
      2 * (translatedCompletionWords C u c ∩
        retainedCompletionWords C v).card := by
  classical
  -- The two original cubes and the two translated cubes are pairwise
  -- disjoint within their respective layers.  The two cross overlaps are
  -- exchanged by flip_c and therefore have equal cardinality.
  have hQQ :=
    loss_original_cubes_disjoint
      C exponent hexp honeLoss huLoss huv
  have hTT :=
    translated_loss_blocks_disjoint_same_coordinate
      C exponent hexp honeLoss huLoss hvLoss huv c
  have hcrossEq :=
    loss_cross_exchange_card_eq C u v c
  have hBu :=
    projectedLoss_doubledBlock_card_eq_target
      C exponent huLoss hcu
  have hBv :=
    projectedLoss_doubledBlock_card_eq_target
      C exponent hvLoss hcv
  rw [Finset.card_union]
  rw [hBu, hBv]
  -- The intersection of the doubled blocks is exactly the disjoint union of
  -- the two cross terms.
  have hinter :
      doubledCompletionBlock C u c ∩
          doubledCompletionBlock C v c
        =
      (translatedCompletionWords C u c ∩
          retainedCompletionWords C v) ∪
      (retainedCompletionWords C u ∩
          translatedCompletionWords C v c) := by
    apply Finset.ext
    intro word
    simp only [doubledCompletionBlock, Finset.mem_inter,
      Finset.mem_union]
    constructor
    · rintro ⟨huQ | huT, hvQ | hvT⟩
      · exact False.elim
          (Finset.disjoint_left.mp hQQ huQ hvQ)
      · exact Or.inr ⟨huQ,hvT⟩
      · exact Or.inl ⟨huT,hvQ⟩
      · exact False.elim
          (Finset.disjoint_left.mp hTT huT hvT)
    · rintro (h | h)
      · exact ⟨Or.inr h.1, Or.inl h.2⟩
      · exact ⟨Or.inl h.1, Or.inr h.2⟩
  rw [hinter]
  have hcrossDisj :
      Disjoint
        (translatedCompletionWords C u c ∩
          retainedCompletionWords C v)
        (retainedCompletionWords C u ∩
          translatedCompletionWords C v c) := by
    rw [Finset.disjoint_left]
    intro word hA hB
    have hAp := Finset.mem_inter.mp hA
    have hBp := Finset.mem_inter.mp hB
    exact Finset.disjoint_left.mp hQQ hBp.1 hAp.2
  rw [Finset.card_union_of_disjoint hcrossDisj,
      hcrossEq]
  omega

#print axioms loss_cross_exchange_card_eq
#print axioms same_coordinate_loss_doubled_union_card

end OrderedEdgeColoring
end JSP000404Research
