import JSP000404Research.ResidualActualCollisionDiagonalExactObstruction
import Mathlib.Tactic

/-!
# Global two-flip collision rigidity and fixed-flip-pair no-double-booking

Two Boolean words may have the same double-flip target under DIFFERENT
ordered flip pairs. We prove that any such equality forces the SOURCE
words to agree outside the union of the FOUR selected coordinates.
This is a necessary obstruction to a globally injective hole payment.
For a FIXED flip pair the map is injective, giving a non-reusing
cardinality capacity for that fibre. Neither theorem claims that
the actual collision-dependent flip pair is globally fixed or that
every target is a global Boolean hole.
-/

namespace JSP000404Research
namespace OrderedEdgeColoring

/-- If two source words share a double-flip target, they agree at
every coordinate outside the four flip coordinates. In particular
a collision of diagonals CANNOT occur when the two words differ
at a fifth, unflipped coordinate. -/
theorem double_flip_target_eq_source_agree_outside_four
    {n : ℕ} (w z : Fin n → Bool)
    (cf₁ cr₁ cf₂ cr₂ : Fin n)
    (heq :
      flipCompletionWord cf₁ (flipCompletionWord cr₁ w) =
      flipCompletionWord cf₂ (flipCompletionWord cr₂ z))
    (e : Fin n)
    (hf₁ : e ≠ cf₁) (hr₁ : e ≠ cr₁)
    (hf₂ : e ≠ cf₂) (hr₂ : e ≠ cr₂) :
    w e = z e := by
  have h := congrArg (fun v : Fin n → Bool => v e) heq
  simpa [flipCompletionWord, flipBoolWordAt, hf₁, hr₁, hf₂, hr₂] using h

/-- A witness to a difference OUTSIDE the four flip coordinates
certifies that the two candidate diagonal targets are distinct,
even though the respective pairs of flips may be different. -/
theorem double_flip_targets_ne_of_source_diff_outside_four
    {n : ℕ} (w z : Fin n → Bool)
    (cf₁ cr₁ cf₂ cr₂ : Fin n)
    (e : Fin n)
    (hf₁ : e ≠ cf₁) (hr₁ : e ≠ cr₁)
    (hf₂ : e ≠ cf₂) (hr₂ : e ≠ cr₂)
    (hneq : w e ≠ z e) :
    flipCompletionWord cf₁ (flipCompletionWord cr₁ w) ≠
      flipCompletionWord cf₂ (flipCompletionWord cr₂ z) := by
  intro heq
  exact hneq (double_flip_target_eq_source_agree_outside_four
    w z cf₁ cr₁ cf₂ cr₂ heq e hf₁ hr₁ hf₂ hr₂)

/-- Within any FIXED ordered pair of flip coordinates, the full
target map injects any chosen source set into its image. In
particular, if every target actually is in the SAME finite hole
budget H, that class is paid by H WITHOUT REUSING ANY WORD.

This does NOT imply that different flip-coordinate classes have
disjoint target images. -/
theorem fixed_two_flip_hole_capacity
    {n : ℕ}
    (sources holes : Finset (Fin n → Bool))
    (cf cr : Fin n)
    (hhole : ∀ w ∈ sources,
      flipCompletionWord cf (flipCompletionWord cr w) ∈ holes) :
    sources.card ≤ holes.card := by
  classical
  have himage :
      sources.image
        (fun w => flipCompletionWord cf (flipCompletionWord cr w))
        ⊆ holes := by
    intro d hd
    obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hd
    exact hhole w hw
  have hcard :
      (sources.image
        (fun w => flipCompletionWord cf (flipCompletionWord cr w))).card =
        sources.card :=
    Finset.card_image_of_injective sources
      (double_flip_completion_word_injective cf cr)
  calc
    sources.card =
        (sources.image
          (fun w => flipCompletionWord cf (flipCompletionWord cr w))).card :=
      hcard.symm
    _ ≤ holes.card := Finset.card_le_card himage


/-- Two classes of source words with possibly DIFFERENT fixed flip
pairs have pairwise DISJOINT target images whenever each cross-class
source pair has a differing coordinate outside all four flip bits.
The condition is concrete and checkable, but not yet proved for
all actual planar collision classes. -/
theorem two_flip_images_disjoint_of_four_coordinate_separation
    {n : ℕ}
    (left right : Finset (Fin n → Bool))
    (cf₁ cr₁ cf₂ cr₂ : Fin n)
    (hsep :
      ∀ w ∈ left, ∀ z ∈ right,
        ∃ e : Fin n,
          e ≠ cf₁ ∧ e ≠ cr₁ ∧
          e ≠ cf₂ ∧ e ≠ cr₂ ∧ w e ≠ z e) :
    Disjoint
      (left.image
        (fun w => flipCompletionWord cf₁ (flipCompletionWord cr₁ w)))
      (right.image
        (fun z => flipCompletionWord cf₂ (flipCompletionWord cr₂ z))) := by
  classical
  apply Finset.disjoint_left.mpr
  intro d hdLeft hdRight
  obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hdLeft
  obtain ⟨z, hz, hzd⟩ := Finset.mem_image.mp hdRight
  obtain ⟨e, hf₁, hr₁, hf₂, hr₂, hne⟩ := hsep w hw z hz
  exact (double_flip_targets_ne_of_source_diff_outside_four
    w z cf₁ cr₁ cf₂ cr₂ e hf₁ hr₁ hf₂ hr₂ hne) hzd.symm

/-- Concrete two-class NON-REUSING hole payment. In addition to
each class having legitimate true-hole diagonal targets, the
four-coordinate source separation certifies their target images
do not overlap. No colour-uniformity or independence is silently
assumed across the classes. -/
theorem separated_two_flip_classes_joint_hole_capacity
    {n : ℕ}
    (left right holes : Finset (Fin n → Bool))
    (cf₁ cr₁ cf₂ cr₂ : Fin n)
    (hleft : ∀ w ∈ left,
      flipCompletionWord cf₁ (flipCompletionWord cr₁ w) ∈ holes)
    (hright : ∀ z ∈ right,
      flipCompletionWord cf₂ (flipCompletionWord cr₂ z) ∈ holes)
    (hsep :
      ∀ w ∈ left, ∀ z ∈ right,
        ∃ e : Fin n,
          e ≠ cf₁ ∧ e ≠ cr₁ ∧
          e ≠ cf₂ ∧ e ≠ cr₂ ∧ w e ≠ z e) :
    left.card + right.card ≤ holes.card := by
  classical
  let L := left.image
    (fun w => flipCompletionWord cf₁ (flipCompletionWord cr₁ w))
  let R := right.image
    (fun z => flipCompletionWord cf₂ (flipCompletionWord cr₂ z))
  have hdisj : Disjoint L R :=
    two_flip_images_disjoint_of_four_coordinate_separation
      left right cf₁ cr₁ cf₂ cr₂ hsep
  have hLcard : L.card = left.card :=
    Finset.card_image_of_injective left
      (double_flip_completion_word_injective cf₁ cr₁)
  have hRcard : R.card = right.card :=
    Finset.card_image_of_injective right
      (double_flip_completion_word_injective cf₂ cr₂)
  have hsubset : L ∪ R ⊆ holes := by
    intro d hd
    rcases Finset.mem_union.mp hd with hdL | hdR
    · obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hdL
      exact hleft w hw
    · obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hdR
      exact hright z hz
  calc
    left.card + right.card = (L ∪ R).card := by
      rw [Finset.card_union_of_disjoint hdisj, hLcard, hRcard]
    _ ≤ holes.card := Finset.card_le_card hsubset

#print axioms two_flip_images_disjoint_of_four_coordinate_separation
#print axioms separated_two_flip_classes_joint_hole_capacity

#print axioms double_flip_target_eq_source_agree_outside_four
#print axioms double_flip_targets_ne_of_source_diff_outside_four
#print axioms fixed_two_flip_hole_capacity

end OrderedEdgeColoring
end JSP000404Research
