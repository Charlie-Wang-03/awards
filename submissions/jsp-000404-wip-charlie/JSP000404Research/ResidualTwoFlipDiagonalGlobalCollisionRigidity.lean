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

#print axioms double_flip_target_eq_source_agree_outside_four
#print axioms double_flip_targets_ne_of_source_diff_outside_four
#print axioms fixed_two_flip_hole_capacity

end OrderedEdgeColoring
end JSP000404Research
