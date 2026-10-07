import JSP000404Research.ResidualBlockerFreeInheritance
import JSP000404Research.ResidualOverlapDimension
import JSP000404Research.BooleanFlipCore
import Mathlib.Tactic

/-!
# Common-inactive directions survive pair-local translation

The explicit saturated-pair maps flip one active coordinate, or two endpoint
active coordinates.  Any common-inactive coordinate of the source overlap pair
is distinct from all such displacement coordinates.

Boolean flips at distinct coordinates commute.  Therefore the translated
images of two source words joined by a common-inactive edge are again joined by
the same Boolean edge.

If one blocker cube contains both translated images, the common-inactive
coordinate is forced to remain inactive at that blocker.
-/

namespace JSP000404Research
namespace OrderedEdgeColoring

theorem commonInactive_ne_active_left
    {V : Type*} [LinearOrder V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    {u v : V} {e c : Fin n}
    (he : e ∈ commonInactiveRetained C u v)
    (hc : c ∈ retainedActive C u) :
    c ≠ e := by
  intro h
  subst c
  exact ((mem_commonInactiveRetained C u v e).1 he).1 hc

theorem commonInactive_ne_active_right
    {V : Type*} [LinearOrder V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    {u v : V} {e d : Fin n}
    (he : e ∈ commonInactiveRetained C u v)
    (hd : d ∈ retainedActive C v) :
    d ≠ e := by
  intro h
  subst d
  exact ((mem_commonInactiveRetained C u v e).1 he).2 hd

theorem one_flip_translation_preserves_commonInactive_edge
    {V : Type*} [LinearOrder V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    {u v : V}
    {word : Fin n → Bool}
    {c e : Fin n}
    (he : e ∈ commonInactiveRetained C u v)
    (hc : c ∈ retainedActive C u) :
    flipBoolWordAt (flipBoolWordAt word e) c =
      flipBoolWordAt (flipBoolWordAt word c) e := by
  have hce : c ≠ e :=
    commonInactive_ne_active_left C he hc
  exact (flipBoolWordAt_commute word hce).symm

theorem two_flip_translation_preserves_commonInactive_edge
    {V : Type*} [LinearOrder V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    {u v : V}
    {word : Fin n → Bool}
    {c d e : Fin n}
    (he : e ∈ commonInactiveRetained C u v)
    (hc : c ∈ retainedActive C u)
    (hd : d ∈ retainedActive C v) :
    flipBoolWordAt
        (flipBoolWordAt (flipBoolWordAt word e) c) d
      =
    flipBoolWordAt
        (flipBoolWordAt (flipBoolWordAt word c) d) e := by
  have hce : c ≠ e :=
    commonInactive_ne_active_left C he hc
  have hde : d ≠ e :=
    commonInactive_ne_active_right C he hd
  calc
    flipBoolWordAt
        (flipBoolWordAt (flipBoolWordAt word e) c) d
      =
    flipBoolWordAt
        (flipBoolWordAt (flipBoolWordAt word c) e) d := by
      exact congrArg
        (fun x => flipBoolWordAt x d)
        (flipBoolWordAt_commute word hce).symm
    _ =
    flipBoolWordAt
        (flipBoolWordAt (flipBoolWordAt word c) d) e := by
      exact
        (flipBoolWordAt_commute
          (flipBoolWordAt word c) hde).symm

theorem blocker_inherits_commonInactive_of_one_flip_pair
    {V : Type*} [LinearOrder V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    {u v w : V}
    {word : Fin n → Bool}
    {c e : Fin n}
    (he : e ∈ commonInactiveRetained C u v)
    (hc : c ∈ retainedActive C u)
    (hy :
      flipBoolWordAt word c ∈
        retainedCompletionWords C w)
    (hyEdge :
      flipBoolWordAt (flipBoolWordAt word e) c ∈
        retainedCompletionWords C w) :
    e ∉ retainedActive C w := by
  have hcomm :=
    one_flip_translation_preserves_commonInactive_edge
      (word := word) C he hc
  rw [hcomm] at hyEdge
  exact inactive_of_word_and_flip_mem_completion
    C hy hyEdge

theorem blocker_inherits_commonInactive_of_two_flip_pair
    {V : Type*} [LinearOrder V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    {u v w : V}
    {word : Fin n → Bool}
    {c d e : Fin n}
    (he : e ∈ commonInactiveRetained C u v)
    (hc : c ∈ retainedActive C u)
    (hd : d ∈ retainedActive C v)
    (hy :
      flipBoolWordAt (flipBoolWordAt word c) d ∈
        retainedCompletionWords C w)
    (hyEdge :
      flipBoolWordAt
          (flipBoolWordAt (flipBoolWordAt word e) c) d
        ∈ retainedCompletionWords C w) :
    e ∉ retainedActive C w := by
  have hcomm :=
    two_flip_translation_preserves_commonInactive_edge
      (word := word) C he hc hd
  rw [hcomm] at hyEdge
  exact inactive_of_word_and_flip_mem_completion
    C hy hyEdge

#print axioms blocker_inherits_commonInactive_of_one_flip_pair
#print axioms blocker_inherits_commonInactive_of_two_flip_pair

end OrderedEdgeColoring
end JSP000404Research
