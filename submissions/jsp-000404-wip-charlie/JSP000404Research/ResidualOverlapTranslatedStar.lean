import JSP000404Research.ResidualPairFlipBlocker
import Mathlib.Tactic

/-!
# Coordinate uniqueness for one-bit blockers across an overlap cube

The zero-zero blocker-star argument does not rely on the source overlap cube
being a singleton.

Let x and y be any two words in Q_u ∩ Q_v.  Suppose c and d are distinct
coordinates, and d is active at both endpoints.  If one blocker Q_w contains
flip_c(x) and flip_d(y), then the d-blocker rule forces the canonical d-bit of
w to be the opposite of the source d-bit.  But flip_c(x) is unchanged at d,
so its membership in Q_w forces the same d-bit as the source. Contradiction.

Hence one blocker cannot serve two distinct translated active-coordinate
families, even when the source words vary freely on common-inactive
coordinates.
-/

namespace JSP000404Research
namespace OrderedEdgeColoring

theorem oneFlip_blocker_coordinate_unique_across_overlap_words
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    {u v w : V}
    (huv : u ≠ v)
    {x y : Fin n → Bool}
    (hxU : x ∈ retainedCompletionWords C u)
    (hxV : x ∈ retainedCompletionWords C v)
    (hyU : y ∈ retainedCompletionWords C u)
    (hyV : y ∈ retainedCompletionWords C v)
    {c d : Fin n}
    (hdU : d ∈ retainedActive C u)
    (hdV : d ∈ retainedActive C v)
    (hwc :
      flipBoolWordAt x c ∈ retainedCompletionWords C w)
    (hwd :
      flipBoolWordAt y d ∈ retainedCompletionWords C w) :
    c = d := by
  by_contra hcd
  have hdW :
      d ∈ retainedActive C w :=
    one_flip_blocker_active
      C huv hyU hyV hdU hdV hwd
  have hdBit :
      retainedBit C w d = !(retainedBit C u d) :=
    one_flip_blocker_bit_eq_not
      C huv hyU hyV hdU hdV hwd
  have hwcComp :=
    (mem_retainedCompletionWords C w
      (flipBoolWordAt x c)).1 hwc
  have hxComp :=
    (mem_retainedCompletionWords C u x).1 hxU
  have hxD :
      x d = retainedBit C u d :=
    hxComp d hdU
  have hwcD :
      flipBoolWordAt x c d = retainedBit C w d :=
    hwcComp d hdW
  have hflipOff :
      flipBoolWordAt x c d = x d :=
    flipBoolWordAt_off x (Ne.symm hcd)
  rw [hflipOff, hxD, hdBit] at hwcD
  cases h : retainedBit C u d <;> simp [h] at hwcD

#print axioms oneFlip_blocker_coordinate_unique_across_overlap_words

end OrderedEdgeColoring
end JSP000404Research
