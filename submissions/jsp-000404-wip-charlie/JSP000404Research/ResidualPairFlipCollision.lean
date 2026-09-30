import JSP000404Research.ResidualPairLocalFlip
import Mathlib.Tactic

/-!
# Boolean normal forms for collisions of local flip maps

Cross-carrier collision analysis reduces first to elementary identities in the
Boolean cube.  If two translated words coincide, then undoing one translation
expresses one source word as a one- or two-coordinate translate of the other.

These lemmas deliberately contain no colouring hypotheses.  They are the
algebraic normal forms used later to turn equality of pair-local displaced
images into overlap constraints between the original carrier cubes.
-/

namespace JSP000404Research
namespace OrderedEdgeColoring

theorem eq_of_one_flip_eq_one_flip
    {n : ℕ}
    {x y : Fin n → Bool}
    {c d : Fin n}
    (h :
      flipBoolWordAt x c =
        flipBoolWordAt y d) :
    x =
      flipBoolWordAt
        (flipBoolWordAt y d) c := by
  calc
    x = flipBoolWordAt (flipBoolWordAt x c) c := by
      symm
      exact flipBoolWordAt_involutive c x
    _ = flipBoolWordAt (flipBoolWordAt y d) c := by
      rw [h]

theorem eq_of_one_flip_eq_one_flip_same
    {n : ℕ}
    {x y : Fin n → Bool}
    {c : Fin n}
    (h :
      flipBoolWordAt x c =
        flipBoolWordAt y c) :
    x = y :=
  flipBoolWordAt_injective c h

theorem eq_of_one_flip_eq_one_flip_distinct
    {n : ℕ}
    {x y : Fin n → Bool}
    {c d : Fin n}
    (hcd : c ≠ d)
    (h :
      flipBoolWordAt x c =
        flipBoolWordAt y d) :
    x =
      flipBoolWordAt
        (flipBoolWordAt y c) d := by
  funext e
  by_cases hec : e = c
  · subst e
    have hc := congrFun h c
    rw [flipBoolWordAt_at,
        flipBoolWordAt_off y hcd.symm] at hc
    rw [flipBoolWordAt_off _ hcd,
        flipBoolWordAt_at]
    cases hx : x c <;> cases hy : y c <;>
      simp [hx, hy] at hc ⊢
  · by_cases hed : e = d
    · subst e
      have hd := congrFun h d
      rw [flipBoolWordAt_off x hcd,
          flipBoolWordAt_at] at hd
      rw [flipBoolWordAt_at,
          flipBoolWordAt_off _ hcd.symm]
      cases hx : x d <;> cases hy : y d <;>
        simp [hx, hy] at hd ⊢
    · have heq := congrFun h e
      rw [flipBoolWordAt_off x hec,
          flipBoolWordAt_off y hed] at heq
      rw [flipBoolWordAt_off _ hed,
          flipBoolWordAt_off y hec]
      exact heq

theorem eq_of_two_flip_eq_one_flip
    {n : ℕ}
    {x y : Fin n → Bool}
    {c d e : Fin n}
    (h :
      flipBoolWordAt (flipBoolWordAt x c) d =
        flipBoolWordAt y e) :
    x =
      flipBoolWordAt
        (flipBoolWordAt
          (flipBoolWordAt y e) d) c := by
  calc
    x =
        flipBoolWordAt
          (flipBoolWordAt
            (flipBoolWordAt
              (flipBoolWordAt x c) d) d) c := by
          rw [flipBoolWordAt_involutive d,
              flipBoolWordAt_involutive c]
    _ =
        flipBoolWordAt
          (flipBoolWordAt
            (flipBoolWordAt y e) d) c := by
          rw [h]

theorem eq_of_two_flip_eq_two_flip
    {n : ℕ}
    {x y : Fin n → Bool}
    {c d e f : Fin n}
    (h :
      flipBoolWordAt (flipBoolWordAt x c) d =
        flipBoolWordAt (flipBoolWordAt y e) f) :
    x =
      flipBoolWordAt
        (flipBoolWordAt
          (flipBoolWordAt
            (flipBoolWordAt y e) f) d) c := by
  calc
    x =
        flipBoolWordAt
          (flipBoolWordAt
            (flipBoolWordAt
              (flipBoolWordAt x c) d) d) c := by
          rw [flipBoolWordAt_involutive d,
              flipBoolWordAt_involutive c]
    _ =
        flipBoolWordAt
          (flipBoolWordAt
            (flipBoolWordAt
              (flipBoolWordAt y e) f) d) c := by
          rw [h]

#print axioms eq_of_one_flip_eq_one_flip
#print axioms eq_of_one_flip_eq_one_flip_same
#print axioms eq_of_one_flip_eq_one_flip_distinct
#print axioms eq_of_two_flip_eq_one_flip
#print axioms eq_of_two_flip_eq_two_flip

end OrderedEdgeColoring
end JSP000404Research
