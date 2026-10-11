import JSP000404Research.ResidualCompletionPairMass
import JSP000404Research.RetainedCompletionCore
import Mathlib.Tactic

/-!
# Exact Boolean-face mass of each residual completion overlap

Suppose two retained partial-code completion cubes meet at one word base.
Their intersection fixes exactly the union of both active coordinate sets,
with prescribed values taken from base. Thus it is a Boolean face with
cardinality exactly 2^(n - card(active_u ∪ active_v)).

Combined with unique residual-edge ownership, this identifies the exact
overlap mass of the entire projected completion family as a sum over
residual edges of positive Boolean face cardinalities.

All statements are elementary but globally composable counting facts.
No planar geometric defect-payment bound is silently assumed.
-/

namespace JSP000404Research
namespace OrderedEdgeColoring

/-- A general n-bit Boolean face fixing coordinates in A to a base word. -/
noncomputable def fixedCoordinateWords
    {n : ℕ} (A : Finset (Fin n))
    (base : Fin n → Bool) : Finset (Fin n → Bool) := by
  classical
  exact Finset.univ.filter
    (fun word => ∀ d, d ∈ A → word d = base d)

@[simp] theorem mem_fixedCoordinateWords
    {n : ℕ} (A : Finset (Fin n))
    (base word : Fin n → Bool) :
    word ∈ fixedCoordinateWords A base ↔
      ∀ d, d ∈ A → word d = base d := by
  classical
  simp [fixedCoordinateWords]

/-- The usual free-coordinate Boolean-function equivalence for one face. -/
noncomputable def fixedCoordinateWordsEquivFree
    {n : ℕ} (A : Finset (Fin n))
    (base : Fin n → Bool) :
    FreeCoordinates A ≃
      {word : Fin n → Bool // word ∈ fixedCoordinateWords A base} where
  toFun free := ⟨
    (fun d => if hd : d ∈ A then base d else free ⟨d,hd⟩),
    by
      apply (mem_fixedCoordinateWords A base _).2
      intro d hd
      simp [hd]⟩
  invFun word := fun d => word.1 d.1
  left_inv free := by
    funext d
    simp [d.2]
  right_inv word := by
    apply Subtype.ext
    funext d
    by_cases hd : d ∈ A
    · have hfixed :=
        (mem_fixedCoordinateWords A base word.1).1 word.2
      simp [hd, hfixed d hd]
    · simp [hd]

/-- An n-bit Boolean face fixing |A| coordinates has exactly
2^(n-|A|) vertices. -/
theorem fixedCoordinateWords_card
    {n : ℕ} (A : Finset (Fin n))
    (base : Fin n → Bool) :
    (fixedCoordinateWords A base).card =
      2 ^ (n - A.card) := by
  classical
  have hcard := Fintype.card_congr
    (fixedCoordinateWordsEquivFree A base)
  rw [card_freeCoordinates] at hcard
  calc
    (fixedCoordinateWords A base).card =
        Fintype.card
          {word : Fin n → Bool //
            word ∈ fixedCoordinateWords A base} := by
          symm
          exact Fintype.card_coe _
    _ = 2 ^ (n - A.card) := hcard.symm

/-- Once a common completion base exists, the intersection
of two completion cubes is exactly the face on the UNION
of their active coordinate sets, fixed to that base. -/
theorem retainedCompletionWords_inter_eq_fixedCoordinateWords
    {V : Type*} [LinearOrder V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (u v : V)
    {base : Fin n → Bool}
    (hu : base ∈ retainedCompletionWords C u)
    (hv : base ∈ retainedCompletionWords C v) :
    retainedCompletionWords C u ∩ retainedCompletionWords C v =
      fixedCoordinateWords
        (retainedActive C u ∪ retainedActive C v) base := by
  classical
  ext word
  constructor
  · intro hw
    obtain ⟨hwu, hwv⟩ := Finset.mem_inter.mp hw
    apply (mem_fixedCoordinateWords _ base word).2
    intro d hd
    rcases Finset.mem_union.mp hd with hdu | hdv
    · exact ((mem_retainedCompletionWords C u word).1 hwu d hdu).trans
        (((mem_retainedCompletionWords C u base).1 hu d hdu).symm)
    · exact ((mem_retainedCompletionWords C v word).1 hwv d hdv).trans
        (((mem_retainedCompletionWords C v base).1 hv d hdv).symm)
  · intro hw
    have hface := (mem_fixedCoordinateWords _ base word).1 hw
    apply Finset.mem_inter.mpr
    constructor
    · apply (mem_retainedCompletionWords C u word).2
      intro d hd
      exact (hface d (Finset.mem_union_left _ hd)).trans
        ((mem_retainedCompletionWords C u base).1 hu d hd)
    · apply (mem_retainedCompletionWords C v word).2
      intro d hd
      exact (hface d (Finset.mem_union_right _ hd)).trans
        ((mem_retainedCompletionWords C v base).1 hv d hd)

/-- The local completion overlap mass is the full Boolean-face mass,
once the two cubes have a common completion. -/
theorem retainedCompletionWords_inter_card_of_nonempty
    {V : Type*} [LinearOrder V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (u v : V)
    (h :
      (retainedCompletionWords C u ∩
        retainedCompletionWords C v).Nonempty) :
    (retainedCompletionWords C u ∩ retainedCompletionWords C v).card =
      2 ^ (n -
        (retainedActive C u ∪ retainedActive C v).card) := by
  obtain ⟨base, hb⟩ := h
  rw [retainedCompletionWords_inter_eq_fixedCoordinateWords
    C u v (Finset.mem_inter.mp hb).1
      (Finset.mem_inter.mp hb).2]
  exact fixedCoordinateWords_card _ base

/-- Uniform formula for an arbitrary pair: either its cubes
do not meet, or their overlap has exact power-of-two size. -/
theorem retainedCompletionWords_inter_card_eq_if
    {V : Type*} [LinearOrder V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (u v : V) :
    (retainedCompletionWords C u ∩ retainedCompletionWords C v).card =
      if (retainedCompletionWords C u ∩
        retainedCompletionWords C v).Nonempty then
        2 ^ (n -
          (retainedActive C u ∪ retainedActive C v).card)
      else 0 := by
  classical
  by_cases h :
      (retainedCompletionWords C u ∩
        retainedCompletionWords C v).Nonempty
  · simpa [h] using
      retainedCompletionWords_inter_card_of_nonempty C u v h
  · have hzero :
        (retainedCompletionWords C u ∩
          retainedCompletionWords C v).card = 0 := by
      by_contra hz
      have hpos :
          0 < (retainedCompletionWords C u ∩
            retainedCompletionWords C v).card := by omega
      exact h (Finset.card_pos.mp hpos)
    simp [h, hzero]

#print axioms fixedCoordinateWords_card
#print axioms retainedCompletionWords_inter_eq_fixedCoordinateWords
#print axioms retainedCompletionWords_inter_card_of_nonempty
#print axioms retainedCompletionWords_inter_card_eq_if

end OrderedEdgeColoring
end JSP000404Research
