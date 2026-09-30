import JSP000404Research.ResidualAugmentingState
import Mathlib.Tactic

/-!
# Branching expansion from two active coordinates of a single fibre

Let word be singly covered by Q_v, and let c,d be two distinct active
coordinates of v.  Consider the two one-bit translates

  y_c = flip_c(word),  y_d = flip_d(word).

Any blocker of y_c must activate c with the bit opposite to v, and any blocker
of y_d must activate d with the bit opposite to v.

No completion cube can block both translated words.  Indeed, if Q_w contained
both y_c and y_d, then the d-blocker rule would force the canonical d-bit of w
to be opposite to v, while membership of y_c in Q_w sees coordinate d
unchanged from the original word and hence equal to v's d-bit.

Thus the two blocker fibres are disjoint.  In particular, if neither translate
is a hole, the two exits create at least two distinct blocking vertices.  This
is the first genuine expansion lemma for the global augmenting/Hall route.
-/

namespace JSP000404Research
namespace OrderedEdgeColoring

theorem two_single_flips_have_disjoint_blocker_fibres
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    {owner : V} {word : Fin n → Bool}
    {c d : Fin n}
    (hsingle : IsSingleCompletionWord C owner word)
    (hc : c ∈ retainedActive C owner)
    (hd : d ∈ retainedActive C owner)
    (hcd : c ≠ d) :
    Disjoint
      (completionFibre C (flipBoolWordAt word c))
      (completionFibre C (flipBoolWordAt word d)) := by
  classical
  rw [Finset.disjoint_left]
  intro w hwc hwd
  have hwcComp :=
    (mem_completionFibre C
      (flipBoolWordAt word c) w).1 hwc
  have hwdComp :=
    (mem_completionFibre C
      (flipBoolWordAt word d) w).1 hwd

  have hdW :=
    single_flip_blocker_active
      C hsingle hd hwdComp
  have hdBit :=
    single_flip_blocker_bit_opposite
      C hsingle hd hwdComp

  have hownerComp :=
    (mem_retainedCompletionWords C owner word).1 hsingle.1
  have hwordD :=
    hownerComp d hd

  have hwcConstraint :=
    (mem_retainedCompletionWords C w
      (flipBoolWordAt word c)).1 hwcComp d hdW
  have hdc : d ≠ c := Ne.symm hcd
  rw [flipBoolWordAt_off word hdc, hwordD] at hwcConstraint
  rw [hdBit] at hwcConstraint
  cases h : retainedBit C owner d <;> simp [h] at hwcConstraint

theorem two_single_flips_nonempty_fibres_give_two_blockers
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    {owner : V} {word : Fin n → Bool}
    {c d : Fin n}
    (hsingle : IsSingleCompletionWord C owner word)
    (hc : c ∈ retainedActive C owner)
    (hd : d ∈ retainedActive C owner)
    (hcd : c ≠ d)
    (hcNonempty :
      (completionFibre C (flipBoolWordAt word c)).Nonempty)
    (hdNonempty :
      (completionFibre C (flipBoolWordAt word d)).Nonempty) :
    ∃ w z : V,
      w ≠ z ∧
      flipBoolWordAt word c ∈ retainedCompletionWords C w ∧
      flipBoolWordAt word d ∈ retainedCompletionWords C z := by
  obtain ⟨w,hw⟩ := hcNonempty
  obtain ⟨z,hz⟩ := hdNonempty
  have hwComp :=
    (mem_completionFibre C
      (flipBoolWordAt word c) w).1 hw
  have hzComp :=
    (mem_completionFibre C
      (flipBoolWordAt word d) z).1 hz
  have hdisj :=
    two_single_flips_have_disjoint_blocker_fibres
      C hsingle hc hd hcd
  have hwz : w ≠ z := by
    intro h
    subst z
    exact Finset.disjoint_left.mp hdisj hw hz
  exact ⟨w,z,hwz,hwComp,hzComp⟩

#print axioms two_single_flips_have_disjoint_blocker_fibres
#print axioms two_single_flips_nonempty_fibres_give_two_blockers

end OrderedEdgeColoring
end JSP000404Research
