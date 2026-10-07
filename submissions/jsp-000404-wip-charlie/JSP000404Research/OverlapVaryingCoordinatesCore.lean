import JSP000404Research.BooleanFlipCore
import Mathlib.Tactic

/-!
# Coordinates that genuinely vary inside a Boolean overlap set

For a finite set S of Boolean words, a coordinate varies when two words of S
take different values there.

A simultaneous flip of one coordinate on every word is a cube translation.
It changes fixed bit values but does not change which coordinates vary.
Therefore the varying-coordinate set is invariant under oneFlipOverlapRel and
its equivalence closure.

This is the support-level invariant behind the overlap translation quotient.
-/

namespace JSP000404Research
namespace OrderedEdgeColoring

noncomputable def overlapVaryingCoordinates
    {n : ℕ}
    (S : Finset (Fin n → Bool)) :
    Finset (Fin n) := by
  classical
  exact Finset.univ.filter fun c =>
    ∃ x ∈ S, ∃ y ∈ S, x c ≠ y c

@[simp] theorem mem_overlapVaryingCoordinates
    {n : ℕ}
    (S : Finset (Fin n → Bool))
    (c : Fin n) :
    c ∈ overlapVaryingCoordinates S ↔
      ∃ x ∈ S, ∃ y ∈ S, x c ≠ y c := by
  classical
  simp [overlapVaryingCoordinates]

theorem flipBoolWordAt_value_ne_iff
    {n : ℕ}
    (x y : Fin n → Bool)
    (c d : Fin n) :
    flipBoolWordAt x c d ≠ flipBoolWordAt y c d
      ↔ x d ≠ y d := by
  by_cases hdc : d = c
  · subst d
    cases hx : x c <;>
      cases hy : y c <;>
      simp [flipBoolWordAt, hx, hy]
  · simp [flipBoolWordAt, hdc]

theorem overlapVaryingCoordinates_image_flip
    {n : ℕ}
    (S : Finset (Fin n → Bool))
    (c : Fin n) :
    overlapVaryingCoordinates
        (S.image (fun word => flipBoolWordAt word c))
      =
    overlapVaryingCoordinates S := by
  classical
  ext d
  simp only [mem_overlapVaryingCoordinates]
  constructor
  · rintro ⟨x,hx,y,hy,hxy⟩
    obtain ⟨x0,hx0,rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨y0,hy0,rfl⟩ := Finset.mem_image.mp hy
    exact ⟨x0,hx0,y0,hy0,
      (flipBoolWordAt_value_ne_iff x0 y0 c d).1 hxy⟩
  · rintro ⟨x,hx,y,hy,hxy⟩
    refine ⟨flipBoolWordAt x c, ?_,
      flipBoolWordAt y c, ?_, ?_⟩
    · exact Finset.mem_image.mpr ⟨x,hx,rfl⟩
    · exact Finset.mem_image.mpr ⟨y,hy,rfl⟩
    · exact (flipBoolWordAt_value_ne_iff x y c d).2 hxy

#print axioms flipBoolWordAt_value_ne_iff
#print axioms overlapVaryingCoordinates_image_flip

end OrderedEdgeColoring
end JSP000404Research
