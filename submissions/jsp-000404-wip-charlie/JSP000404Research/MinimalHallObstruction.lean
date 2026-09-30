import Mathlib.Combinatorics.Hall.Finite
import Mathlib.Tactic

/-!
# Minimal Hall obstructions for finite augmenting arguments

Let targets(x) be the finite set of admissible targets for demand x.  A Hall
deficient set S satisfies

  card (union_{x in S} targets(x)) < card S.

If S is inclusion-minimal among deficient sets, then its neighbourhood has
deficiency exactly one:

  card N(S) = card S - 1.

More strongly, deleting any one demand x from S does not shrink the
neighbourhood:

  N(S \ {x}) = N(S).

Consequently every target appearing in a minimal Hall obstruction is supported
by another demand after any chosen demand is removed.  In particular, no
target can be unique to one member of the obstruction.

This is the finite augmenting-path rigidity needed for the final JSP-000404
hard-word matching argument.
-/

namespace JSP000404Research

open scoped BigOperators

namespace FiniteHall

variable {A B : Type*} [Fintype A] [Fintype B]
variable [DecidableEq A] [DecidableEq B]

def Deficient
    (targets : A → Finset B)
    (S : Finset A) : Prop :=
  (S.biUnion targets).card < S.card

def InclusionMinimalDeficient
    (targets : A → Finset B)
    (S : Finset A) : Prop :=
  Deficient targets S ∧
    ∀ T : Finset A, T ⊂ S → ¬ Deficient targets T

theorem deficient_nonempty
    (targets : A → Finset B)
    {S : Finset A}
    (hS : Deficient targets S) :
    S.Nonempty := by
  by_contra hne
  have hzero : S = ∅ :=
    Finset.not_nonempty_iff_eq_empty.mp hne
  subst S
  simp [Deficient] at hS

theorem biUnion_mono
    (targets : A → Finset B)
    {S T : Finset A}
    (hST : S ⊆ T) :
    S.biUnion targets ⊆ T.biUnion targets := by
  intro y hy
  obtain ⟨x, hxS, hyx⟩ := Finset.mem_biUnion.mp hy
  exact Finset.mem_biUnion.mpr ⟨x, hST hxS, hyx⟩

/-- A minimal deficient family has deficiency exactly one. -/
theorem minimalDeficient_neighborhood_card_eq
    (targets : A → Finset B)
    {S : Finset A}
    (hmin : InclusionMinimalDeficient targets S) :
    (S.biUnion targets).card = S.card - 1 := by
  classical
  have hne : S.Nonempty :=
    deficient_nonempty targets hmin.1
  obtain ⟨x, hxS⟩ := hne
  let T := S.erase x
  have hTS : T ⊂ S := by
    constructor
    · exact Finset.erase_subset x S
    · intro hEq
      have hxNot : x ∉ S.erase x := by simp
      exact hxNot (by rw [hEq]; exact hxS)
  have hTnot : ¬ Deficient targets T :=
    hmin.2 T hTS
  have hTcard :
      T.card ≤ (T.biUnion targets).card := by
    unfold Deficient at hTnot
    omega
  have hmono :
      (T.biUnion targets).card ≤
        (S.biUnion targets).card :=
    Finset.card_le_card
      (biUnion_mono targets (Finset.erase_subset x S))
  have hEraseCard : T.card = S.card - 1 := by
    dsimp [T]
    rw [Finset.card_erase_of_mem hxS]
  have hDef : (S.biUnion targets).card < S.card :=
    hmin.1
  omega

/-- Removing any one demand from a minimal deficient family leaves exactly the
same target neighbourhood. -/
theorem minimalDeficient_biUnion_erase_eq
    (targets : A → Finset B)
    {S : Finset A}
    (hmin : InclusionMinimalDeficient targets S)
    {x : A}
    (hxS : x ∈ S) :
    ((S.erase x).biUnion targets) =
      S.biUnion targets := by
  classical
  have hproper : S.erase x ⊂ S := by
    constructor
    · exact Finset.erase_subset x S
    · intro hEq
      have hxNot : x ∉ S.erase x := by simp
      exact hxNot (by rw [hEq]; exact hxS)
  have hnot :
      ¬ Deficient targets (S.erase x) :=
    hmin.2 (S.erase x) hproper
  have hLower :
      (S.erase x).card ≤
        ((S.erase x).biUnion targets).card := by
    unfold Deficient at hnot
    omega
  have hUpper :
      ((S.erase x).biUnion targets).card ≤
        (S.biUnion targets).card :=
    Finset.card_le_card
      (biUnion_mono targets (Finset.erase_subset x S))
  have hSCard :=
    minimalDeficient_neighborhood_card_eq targets hmin
  have hErase :
      (S.erase x).card = S.card - 1 := by
    rw [Finset.card_erase_of_mem hxS]
  have hCardEq :
      ((S.erase x).biUnion targets).card =
        (S.biUnion targets).card := by
    omega
  apply Finset.Subset.antisymm
  · exact biUnion_mono targets (Finset.erase_subset x S)
  · exact Finset.eq_of_subset_of_card_le
      (biUnion_mono targets (Finset.erase_subset x S))
      (by omega)

/-- Every target in a minimal Hall obstruction is still represented after any
chosen demand is removed. -/
theorem minimalDeficient_target_survives_erase
    (targets : A → Finset B)
    {S : Finset A}
    (hmin : InclusionMinimalDeficient targets S)
    {x : A} (hxS : x ∈ S)
    {y : B}
    (hy : y ∈ S.biUnion targets) :
    y ∈ (S.erase x).biUnion targets := by
  rw [minimalDeficient_biUnion_erase_eq targets hmin hxS]
  exact hy

/-- Hence a target used by x inside a minimal obstruction is also available to
a distinct demand x'. -/
theorem minimalDeficient_no_unique_target
    (targets : A → Finset B)
    {S : Finset A}
    (hmin : InclusionMinimalDeficient targets S)
    {x : A} (hxS : x ∈ S)
    {y : B}
    (hyx : y ∈ targets x) :
    ∃ x' ∈ S, x' ≠ x ∧ y ∈ targets x' := by
  have hyS : y ∈ S.biUnion targets :=
    Finset.mem_biUnion.mpr ⟨x, hxS, hyx⟩
  have hyErase :=
    minimalDeficient_target_survives_erase
      targets hmin hxS hyS
  obtain ⟨x', hxErase, hyx'⟩ :=
    Finset.mem_biUnion.mp hyErase
  have hxData := Finset.mem_erase.mp hxErase
  exact ⟨x', hxData.2, hxData.1, hyx'⟩

#print axioms minimalDeficient_neighborhood_card_eq
#print axioms minimalDeficient_biUnion_erase_eq
#print axioms minimalDeficient_no_unique_target

end FiniteHall
end JSP000404Research
