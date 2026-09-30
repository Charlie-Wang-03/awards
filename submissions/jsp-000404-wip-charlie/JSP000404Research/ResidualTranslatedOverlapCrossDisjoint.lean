import JSP000404Research.ResidualTranslatedOverlapFullSuccessor
import JSP000404Research.ResidualPairFlipBlocker
import Mathlib.Tactic

/-!
# Full one-bit successors are cross-disjoint from the source carrier

In the genuine one-bit pair-local branch the displacement coordinate is active
at both source endpoints.  Every blocker of the displaced word then has a
completion cube globally disjoint from each source endpoint cube.

Hence two full blockers form a new residual successor pair whose two endpoint
cubes are each disjoint from both source endpoint cubes.  In particular all
four source/successor vertices are distinct.
-/

namespace JSP000404Research
namespace OrderedEdgeColoring

theorem oneFlip_fullBlocker_disjoint_source_pair
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    {u v w : V} {c : Fin n}
    {base : Fin n → Bool}
    (huv : u ≠ v)
    (hbase :
      base ∈ retainedCompletionWords C u ∩
        retainedCompletionWords C v)
    (hcu : c ∈ retainedActive C u)
    (hcv : c ∈ retainedActive C v)
    (hfull :
      w ∈ oneFlipFullBlockers C u v c) :
    Disjoint
        (retainedCompletionWords C u)
        (retainedCompletionWords C w)
      ∧
    Disjoint
        (retainedCompletionWords C v)
        (retainedCompletionWords C w)
      ∧
    w ≠ u ∧ w ≠ v := by
  have hbaseParts := Finset.mem_inter.mp hbase
  have hwFlip :=
    oneFlip_fullBlocker_contains_base
      C hbase hfull
  have hdisj :=
    one_flip_blocker_disjoint_both
      C huv hbaseParts.1 hbaseParts.2
      hcu hcv hwFlip
  have hwu : w ≠ u := by
    intro h
    subst w
    exact flip_active_not_mem_completion
      C hbaseParts.1 hcu hwFlip
  have hwv : w ≠ v := by
    intro h
    subst w
    exact flip_active_not_mem_completion
      C hbaseParts.2 hcv hwFlip
  exact ⟨hdisj.1,hdisj.2,hwu,hwv⟩

theorem oneFlip_two_fullBlockers_cross_disjoint_successor
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    {u v w z : V} {c : Fin n}
    {base : Fin n → Bool}
    (huv : u ≠ v)
    (hbase :
      base ∈ retainedCompletionWords C u ∩
        retainedCompletionWords C v)
    (hcu : c ∈ retainedActive C u)
    (hcv : c ∈ retainedActive C v)
    (hwFull :
      w ∈ oneFlipFullBlockers C u v c)
    (hzFull :
      z ∈ oneFlipFullBlockers C u v c)
    (hwz : w ≠ z) :
    (IsResidual C w z ∨ IsResidual C z w) ∧
    commonInactiveRetained C u v ⊆ retainedInactive C w ∧
    commonInactiveRetained C u v ⊆ retainedInactive C z ∧
    Disjoint
      (retainedCompletionWords C u)
      (retainedCompletionWords C w) ∧
    Disjoint
      (retainedCompletionWords C v)
      (retainedCompletionWords C w) ∧
    Disjoint
      (retainedCompletionWords C u)
      (retainedCompletionWords C z) ∧
    Disjoint
      (retainedCompletionWords C v)
      (retainedCompletionWords C z) ∧
    w ≠ u ∧ w ≠ v ∧ z ≠ u ∧ z ≠ v := by
  have hsucc :=
    oneFlip_two_fullBlockers_residual_successor
      C hbase hcu hwFull hzFull hwz
  have hwData :=
    oneFlip_fullBlocker_disjoint_source_pair
      C huv hbase hcu hcv hwFull
  have hzData :=
    oneFlip_fullBlocker_disjoint_source_pair
      C huv hbase hcu hcv hzFull
  exact ⟨
    hsucc.2.2.1,
    hsucc.1,
    hsucc.2.1,
    hwData.1,
    hwData.2.1,
    hzData.1,
    hzData.2.1,
    hwData.2.2.1,
    hwData.2.2.2,
    hzData.2.2.1,
    hzData.2.2.2
  ⟩

#print axioms oneFlip_fullBlocker_disjoint_source_pair
#print axioms oneFlip_two_fullBlockers_cross_disjoint_successor

end OrderedEdgeColoring
end JSP000404Research
