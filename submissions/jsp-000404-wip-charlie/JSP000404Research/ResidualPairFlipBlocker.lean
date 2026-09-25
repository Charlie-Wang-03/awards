
import JSP000404Research.ResidualPairLocalFlip
import JSP000404Research.ResidualCompletionMultiplicity
import Mathlib.Tactic

/-!
# Blockers of explicit pair-local Hamming displacements

Let x be a retained completion word shared by two distinct vertices u,v.

One-bit case.
If c is active at both endpoints and y is obtained from x by flipping c, then
y leaves both endpoint cubes.  Suppose y is nevertheless covered by a third
cube Q_w.

Then c must be active at w.  Otherwise Q_w does not constrain c, so changing
c back would show x in Q_w as well.  But x already lies in Q_u and Q_v,
contradicting completion multiplicity at most two.

Moreover the canonical retained bit of w at c is exactly the opposite of the
endpoint bit.

Two-bit case.
Suppose c is active at u, d is active at v, c!=d, and y is obtained by
flipping both c and d.  Any blocker Q_w must activate at least one of c,d.
If both were inactive at w, both flips could be undone without violating any
constraint of Q_w, again producing a forbidden triple cover of x.

These are the first genuine propagation laws for a global augmenting-path
proof of the final residual hard-word-to-hole payment.
-/

namespace JSP000404Research
namespace OrderedEdgeColoring

/-- If a completion cube does not constrain c, membership is unchanged by
flipping c. -/
theorem mem_completion_iff_flip_of_inactive
    {V : Type*} [LinearOrder V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    {w : V} {word : Fin n → Bool} {c : Fin n}
    (hc : c ∉ retainedActive C w) :
    flipBoolWordAt word c ∈ retainedCompletionWords C w ↔
      word ∈ retainedCompletionWords C w := by
  constructor
  · intro hflip
    apply (mem_retainedCompletionWords C w word).2
    intro d hd
    have hdc : d ≠ c := by
      intro h
      subst d
      exact hc hd
    have hcomp :=
      (mem_retainedCompletionWords C w
        (flipBoolWordAt word c)).1 hflip
    have hdEq := hcomp d hd
    rw [flipBoolWordAt_off word hdc] at hdEq
    exact hdEq
  · intro hword
    apply (mem_retainedCompletionWords C w
      (flipBoolWordAt word c)).2
    intro d hd
    have hdc : d ≠ c := by
      intro h
      subst d
      exact hc hd
    have hcomp :=
      (mem_retainedCompletionWords C w word).1 hword
    rw [flipBoolWordAt_off word hdc]
    exact hcomp d hd

/-- A blocker of a one-bit pair displacement must activate the flipped
coordinate. -/
theorem one_flip_blocker_active
    {V : Type*} [LinearOrder V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    {u v w : V}
    (huv : u ≠ v)
    {word : Fin n → Bool} {c : Fin n}
    (huWord : word ∈ retainedCompletionWords C u)
    (hvWord : word ∈ retainedCompletionWords C v)
    (hcu : c ∈ retainedActive C u)
    (hcv : c ∈ retainedActive C v)
    (hwFlip :
      flipBoolWordAt word c ∈
        retainedCompletionWords C w) :
    c ∈ retainedActive C w := by
  by_contra hcW
  have hwWord :
      word ∈ retainedCompletionWords C w :=
    (mem_completion_iff_flip_of_inactive C hcW).1 hwFlip
  have huw : u ≠ w := by
    intro huw
    subst w
    exact (flip_active_not_mem_completion
      C huWord hcu) hwFlip
  have hvw : v ≠ w := by
    intro hvw
    subst w
    exact (flip_active_not_mem_completion
      C hvWord hcv) hwFlip
  exact no_three_distinct_share_retained_completion
    C huv huw hvw huWord hvWord hwWord

/-- The blocker bit on the captured coordinate is the opposite endpoint bit. -/
theorem one_flip_blocker_bit_eq_not
    {V : Type*} [LinearOrder V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    {u v w : V}
    (huv : u ≠ v)
    {word : Fin n → Bool} {c : Fin n}
    (huWord : word ∈ retainedCompletionWords C u)
    (hvWord : word ∈ retainedCompletionWords C v)
    (hcu : c ∈ retainedActive C u)
    (hcv : c ∈ retainedActive C v)
    (hwFlip :
      flipBoolWordAt word c ∈
        retainedCompletionWords C w) :
    retainedBit C w c = !(retainedBit C u c) := by
  have hcW :=
    one_flip_blocker_active
      C huv huWord hvWord hcu hcv hwFlip
  have hwComp :=
    (mem_retainedCompletionWords C w
      (flipBoolWordAt word c)).1 hwFlip
  have huComp :=
    (mem_retainedCompletionWords C u word).1 huWord
  have hwAt := hwComp c hcW
  have huAt := huComp c hcu
  rw [flipBoolWordAt_at, huAt] at hwAt
  exact hwAt.symm

/-- Package: a one-bit blocker captures c and reverses its endpoint bit. -/
theorem one_flip_blocker_capture
    {V : Type*} [LinearOrder V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    {u v w : V}
    (huv : u ≠ v)
    {word : Fin n → Bool} {c : Fin n}
    (huWord : word ∈ retainedCompletionWords C u)
    (hvWord : word ∈ retainedCompletionWords C v)
    (hcu : c ∈ retainedActive C u)
    (hcv : c ∈ retainedActive C v)
    (hwFlip :
      flipBoolWordAt word c ∈
        retainedCompletionWords C w) :
    c ∈ retainedActive C w ∧
      retainedBit C w c = !(retainedBit C u c) := by
  exact ⟨
    one_flip_blocker_active
      C huv huWord hvWord hcu hcv hwFlip,
    one_flip_blocker_bit_eq_not
      C huv huWord hvWord hcu hcv hwFlip⟩

/-- If a completion cube constrains neither c nor d, a two-bit translation
does not change membership. -/
theorem mem_completion_iff_two_flip_of_both_inactive
    {V : Type*} [LinearOrder V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    {w : V} {word : Fin n → Bool} {c d : Fin n}
    (hc : c ∉ retainedActive C w)
    (hd : d ∉ retainedActive C w) :
    flipBoolWordAt (flipBoolWordAt word c) d ∈
        retainedCompletionWords C w
      ↔
    word ∈ retainedCompletionWords C w := by
  rw [mem_completion_iff_flip_of_inactive C hd,
      mem_completion_iff_flip_of_inactive C hc]

/-- A blocker of a two-bit pair displacement must activate at least one flipped
coordinate. -/
theorem two_flip_blocker_active_one
    {V : Type*} [LinearOrder V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    {u v w : V}
    (huv : u ≠ v)
    {word : Fin n → Bool} {c d : Fin n}
    (hcd : c ≠ d)
    (huWord : word ∈ retainedCompletionWords C u)
    (hvWord : word ∈ retainedCompletionWords C v)
    (hcu : c ∈ retainedActive C u)
    (hdv : d ∈ retainedActive C v)
    (hwFlip :
      flipBoolWordAt (flipBoolWordAt word c) d ∈
        retainedCompletionWords C w) :
    c ∈ retainedActive C w ∨
      d ∈ retainedActive C w := by
  by_contra hnone
  push_neg at hnone
  have hwWord :
      word ∈ retainedCompletionWords C w :=
    (mem_completion_iff_two_flip_of_both_inactive
      C hnone.1 hnone.2).1 hwFlip
  have huw : u ≠ w := by
    intro huw
    subst w
    exact (two_flip_first_active_not_mem_completion
      C huWord hcu hcd) hwFlip
  have hvw : v ≠ w := by
    intro hvw
    subst w
    exact (two_flip_second_active_not_mem_completion
      C hvWord hdv hcd) hwFlip
  exact no_three_distinct_share_retained_completion
    C huv huw hvw huWord hvWord hwWord

/-- If the blocker activates c, its c-bit is the flipped value, provided
d is distinct from c. -/
theorem two_flip_blocker_bit_at_first
    {V : Type*} [LinearOrder V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    {u w : V}
    {word : Fin n → Bool} {c d : Fin n}
    (hcd : c ≠ d)
    (huWord : word ∈ retainedCompletionWords C u)
    (hcu : c ∈ retainedActive C u)
    (hcW : c ∈ retainedActive C w)
    (hwFlip :
      flipBoolWordAt (flipBoolWordAt word c) d ∈
        retainedCompletionWords C w) :
    retainedBit C w c = !(retainedBit C u c) := by
  have hwComp :=
    (mem_retainedCompletionWords C w
      (flipBoolWordAt (flipBoolWordAt word c) d)).1 hwFlip
  have huComp :=
    (mem_retainedCompletionWords C u word).1 huWord
  have hwAt := hwComp c hcW
  have huAt := huComp c hcu
  rw [flipBoolWordAt_two_off_first word hcd, huAt] at hwAt
  exact hwAt.symm

/-- If the blocker activates d, its d-bit is the flipped value. -/
theorem two_flip_blocker_bit_at_second
    {V : Type*} [LinearOrder V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    {v w : V}
    {word : Fin n → Bool} {c d : Fin n}
    (hcd : c ≠ d)
    (hvWord : word ∈ retainedCompletionWords C v)
    (hdv : d ∈ retainedActive C v)
    (hdW : d ∈ retainedActive C w)
    (hwFlip :
      flipBoolWordAt (flipBoolWordAt word c) d ∈
        retainedCompletionWords C w) :
    retainedBit C w d = !(retainedBit C v d) := by
  have hwComp :=
    (mem_retainedCompletionWords C w
      (flipBoolWordAt (flipBoolWordAt word c) d)).1 hwFlip
  have hvComp :=
    (mem_retainedCompletionWords C v word).1 hvWord
  have hwAt := hwComp d hdW
  have hvAt := hvComp d hdv
  have hinner :
      flipBoolWordAt word c d = word d :=
    flipBoolWordAt_off word hcd.symm
  rw [flipBoolWordAt_at, hinner, hvAt] at hwAt
  exact hwAt.symm

#print axioms mem_completion_iff_flip_of_inactive
#print axioms one_flip_blocker_capture
#print axioms mem_completion_iff_two_flip_of_both_inactive
#print axioms two_flip_blocker_active_one
#print axioms two_flip_blocker_bit_at_first
#print axioms two_flip_blocker_bit_at_second

end OrderedEdgeColoring
end JSP000404Research
