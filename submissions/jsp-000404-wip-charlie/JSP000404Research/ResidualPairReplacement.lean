import JSP000404Research.ResidualPairFlipBlocker
import JSP000404Research.ResidualCompletionAccounting
import Mathlib.Tactic

/-!
# Pair replacement after flipping a common active coordinate

Let x lie in two retained completion cubes Q_u and Q_v, and suppose retained
coordinate c is active at both endpoints. Flipping c leaves both old cubes.

If the flipped word y is nevertheless double-covered, its two new carrier
vertices are necessarily distinct from u and v. Moreover each new carrier
activates c with the opposite canonical bit. Hence each new completion cube
is disjoint from each old completion cube.

Thus a blocked common-active flip does not merely move an overlap word: it
replaces the old overlap pair by a completely c-separated new pair. This is
the basic non-cycle structure needed for global pair displacement.
-/

namespace JSP000404Research
namespace OrderedEdgeColoring

theorem common_active_flip_blocker_capture
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
      flipBoolWordAt word c ∈ retainedCompletionWords C w) :
    w ≠ u ∧
    w ≠ v ∧
    c ∈ retainedActive C w ∧
    retainedBit C w c = !(retainedBit C u c) ∧
    Disjoint
      (retainedCompletionWords C u)
      (retainedCompletionWords C w) ∧
    Disjoint
      (retainedCompletionWords C v)
      (retainedCompletionWords C w) := by
  have hwu : w ≠ u := by
    intro h
    subst w
    exact (flip_active_not_mem_completion
      C huWord hcu) hwFlip
  have hwv : w ≠ v := by
    intro h
    subst w
    exact (flip_active_not_mem_completion
      C hvWord hcv) hwFlip
  have hcap :=
    one_flip_blocker_capture
      C huv huWord hvWord hcu hcv hwFlip
  have hdisj :=
    one_flip_blocker_disjoint_both
      C huv huWord hvWord hcu hcv hwFlip
  exact ⟨hwu, hwv, hcap.1, hcap.2,
    hdisj.1, hdisj.2⟩

theorem common_active_flip_overlap_replaces_pair
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    {u v : V}
    (huv : u ≠ v)
    {word : Fin n → Bool} {c : Fin n}
    (huWord : word ∈ retainedCompletionWords C u)
    (hvWord : word ∈ retainedCompletionWords C v)
    (hcu : c ∈ retainedActive C u)
    (hcv : c ∈ retainedActive C v)
    (hoverlap :
      flipBoolWordAt word c ∈ overlapCompletionWords C) :
    ∃ w z : V,
      w ≠ z ∧
      w ≠ u ∧ w ≠ v ∧
      z ≠ u ∧ z ≠ v ∧
      flipBoolWordAt word c ∈ retainedCompletionWords C w ∧
      flipBoolWordAt word c ∈ retainedCompletionWords C z ∧
      c ∈ retainedActive C w ∧
      c ∈ retainedActive C z ∧
      retainedBit C w c = !(retainedBit C u c) ∧
      retainedBit C z c = !(retainedBit C u c) ∧
      Disjoint
        (retainedCompletionWords C u)
        (retainedCompletionWords C w) ∧
      Disjoint
        (retainedCompletionWords C u)
        (retainedCompletionWords C z) ∧
      Disjoint
        (retainedCompletionWords C v)
        (retainedCompletionWords C w) ∧
      Disjoint
        (retainedCompletionWords C v)
        (retainedCompletionWords C z) := by
  obtain ⟨w,z,hwz,_hres,hwWord,hzWord,_huniq⟩ :=
    exists_ordered_residual_pair_of_overlapWord C hoverlap
  have hwCap :=
    common_active_flip_blocker_capture
      C huv huWord hvWord hcu hcv hwWord
  have hzCap :=
    common_active_flip_blocker_capture
      C huv huWord hvWord hcu hcv hzWord
  exact ⟨w,z,ne_of_lt hwz,
    hwCap.1,hwCap.2.1,
    hzCap.1,hzCap.2.1,
    hwWord,hzWord,
    hwCap.2.2.1,hzCap.2.2.1,
    hwCap.2.2.2.1,hzCap.2.2.2.1,
    hwCap.2.2.2.2.1,hzCap.2.2.2.2.1,
    hwCap.2.2.2.2.2,hzCap.2.2.2.2.2⟩

#print axioms common_active_flip_blocker_capture
#print axioms common_active_flip_overlap_replaces_pair

end OrderedEdgeColoring
end JSP000404Research
