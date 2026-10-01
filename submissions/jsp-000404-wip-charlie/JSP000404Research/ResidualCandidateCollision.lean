import JSP000404Research.ResidualLocalCandidateCapacity
import JSP000404Research.MinimalBlockSharedDeficit
import Mathlib.Tactic

/-!
# Collision classification for completion/doubled candidate blocks

Suppose every vertex candidate block is either

  Q_v

or

  Q_v union flip_c(Q_v)

for one retained-active coordinate c.

Any word shared by the candidate blocks of two distinct vertices i,j then lies
in exactly one of the four elementary collision types (not necessarily
exclusively as propositions):

  original--original:
      Q_i ∩ Q_j,

  original--translated:
      Q_i ∩ flip_d(Q_j),

  translated--original:
      flip_c(Q_i) ∩ Q_j,

  translated--translated:
      flip_c(Q_i) ∩ flip_d(Q_j).

This is the common interface joining the minimal Hall-obstruction analysis to
the previously developed residual-overlap and projected-loss blocker geometry.
-/

namespace JSP000404Research
namespace OrderedEdgeColoring

def CandidateBlockShape
    {V : Type*} [LinearOrder V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (blocks : V → Finset (Fin n → Bool))
    (v : V) : Prop :=
  blocks v = retainedCompletionWords C v
  ∨
  ∃ c : Fin n,
    c ∈ retainedActive C v ∧
    blocks v = doubledCompletionBlock C v c

theorem sharedBlockWords_has_other_block
    {V W : Type*} [Fintype V] [DecidableEq V] [DecidableEq W]
    (blocks : V → Finset W)
    {T : Finset V} {v : V} {word : W}
    (hshared : word ∈ sharedBlockWords blocks T v) :
    word ∈ blocks v ∧
    ∃ w : V,
      w ∈ T ∧
      w ≠ v ∧
      word ∈ blocks w := by
  classical
  have hparts := Finset.mem_inter.mp hshared
  rcases Finset.mem_biUnion.mp hparts.2 with ⟨w,hwErase,hword⟩
  have hwData := Finset.mem_erase.mp hwErase
  exact ⟨hparts.1,⟨w,hwData.2,hwData.1,hword⟩⟩

theorem candidateShape_membership_split
    {V : Type*} [LinearOrder V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (blocks : V → Finset (Fin n → Bool))
    {v : V}
    (hshape : CandidateBlockShape C blocks v)
    {word : Fin n → Bool}
    (hword : word ∈ blocks v) :
    word ∈ retainedCompletionWords C v
    ∨
    ∃ c : Fin n,
      c ∈ retainedActive C v ∧
      word ∈ translatedCompletionWords C v c := by
  rcases hshape with horig | hdoubled
  · left
    simpa [horig] using hword
  · obtain ⟨c,hc,hblock⟩ := hdoubled
    rw [hblock] at hword
    unfold doubledCompletionBlock at hword
    rcases Finset.mem_union.mp hword with hQ | hT
    · exact Or.inl hQ
    · exact Or.inr ⟨c,hc,hT⟩

theorem shared_candidate_collision_four_way
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (blocks : V → Finset (Fin n → Bool))
    (hshape : ∀ v, CandidateBlockShape C blocks v)
    {T : Finset V} {i : V} {word : Fin n → Bool}
    (hshared : word ∈ sharedBlockWords blocks T i) :
    ∃ j : V,
      j ∈ T ∧
      j ≠ i ∧
      (
        (
          word ∈ retainedCompletionWords C i ∧
          word ∈ retainedCompletionWords C j
        )
        ∨
        (
          word ∈ retainedCompletionWords C i ∧
          ∃ d : Fin n,
            d ∈ retainedActive C j ∧
            word ∈ translatedCompletionWords C j d
        )
        ∨
        (
          (∃ c : Fin n,
            c ∈ retainedActive C i ∧
            word ∈ translatedCompletionWords C i c) ∧
          word ∈ retainedCompletionWords C j
        )
        ∨
        (
          ∃ c d : Fin n,
            c ∈ retainedActive C i ∧
            d ∈ retainedActive C j ∧
            word ∈ translatedCompletionWords C i c ∧
            word ∈ translatedCompletionWords C j d
        )
      ) := by
  obtain ⟨hiWord,j,hjT,hji,hjWord⟩ :=
    sharedBlockWords_has_other_block blocks hshared
  have hiSplit :=
    candidateShape_membership_split
      C blocks (hshape i) hiWord
  have hjSplit :=
    candidateShape_membership_split
      C blocks (hshape j) hjWord
  refine ⟨j,hjT,hji,?_⟩
  rcases hiSplit with hiQ | hiT
  · rcases hjSplit with hjQ | hjT'
    · exact Or.inl ⟨hiQ,hjQ⟩
    · right
      left
      exact ⟨hiQ,hjT'⟩
  · rcases hjSplit with hjQ | hjT'
    · exact Or.inr (Or.inr (Or.inl ⟨hiT,hjQ⟩))
    · right
      right
      right
      obtain ⟨c,hci,hiTc⟩ := hiT
      obtain ⟨d,hdj,hjTd⟩ := hjT'
      exact ⟨c,d,hci,hdj,hiTc,hjTd⟩

#print axioms sharedBlockWords_has_other_block
#print axioms candidateShape_membership_split
#print axioms shared_candidate_collision_four_way

end OrderedEdgeColoring
end JSP000404Research
