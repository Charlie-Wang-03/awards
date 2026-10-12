import JSP000404Research.ResidualStrictShellSoftMassLedger
import Mathlib.Tactic

/-!
# Reserve-aware global conservation in strict-rigid lower shells

Let U be all strict-rigid lower completion slots after removing the
corresponding upper hard overlap faces. The known per-carrier
singleton/outgoing-soft identity upgrades to a global disjoint ledger.

Crucially, BRIDGE soft words and singleton words in U are disjoint.
We can therefore retain the singleton portion as a certified
deduction from the strict descent gap, rather than counting the
whole gap as possible bridge capacity:

  bridgeSoftMass + singletonInStrictShellMass
     <= SUM_strict (2^k(lower) - 2^k(upper)).

This is strictly stronger than the old bridgeSoftMass <= strict gap,
where shell singletons are present. Both categories are already
covered; the resulting bound is NOT a true-hole or surplus payment.
-/

namespace JSP000404Research
namespace OrderedEdgeColoring

noncomputable def strictShellSingletonWords
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ) : Finset (Fin n → Bool) :=
  netStrictRigidUnusedLowerWords C exponent ∩
    singletonCompletionWords C

noncomputable def strictShellSoftWords
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ) : Finset (Fin n → Bool) :=
  netStrictRigidUnusedLowerWords C exponent ∩
    softOverlapCompletionWords C

/-- The global unused strict-rigid lower-cube slots are EXACTLY a
disjoint union of singleton-covered and soft-overlapped words. -/
theorem strict_shell_global_singleton_soft_partition
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ) :
    netStrictRigidUnusedLowerWords C exponent =
      strictShellSingletonWords C exponent ∪
        strictShellSoftWords C exponent := by
  classical
  ext word
  constructor
  · intro hw
    rcases Finset.mem_union.mp
      (unused_strict_lower_words_subset_singleton_soft C exponent hw)
      with hs | hsoft
    · exact Finset.mem_union.mpr
        (Or.inl (Finset.mem_inter.mpr ⟨hw, hs⟩))
    · exact Finset.mem_union.mpr
        (Or.inr (Finset.mem_inter.mpr ⟨hw, hsoft⟩))
  · intro hw
    rcases Finset.mem_union.mp hw with hs | hsoft
    · exact (Finset.mem_inter.mp hs).1
    · exact (Finset.mem_inter.mp hsoft).1

/-- This partition is really disjoint: completion multiplicity
cannot be both one and two. -/
theorem strict_shell_global_singleton_soft_disjoint
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ) :
    Disjoint (strictShellSingletonWords C exponent)
      (strictShellSoftWords C exponent) := by
  classical
  apply Finset.disjoint_left.mpr
  intro word hs hsoft
  have hone : (completionFibre C word).card = 1 :=
    (mem_singletonCompletionWords C word).1
      (Finset.mem_inter.mp hs).2
  have hoverlap : word ∈ overlapCompletionWords C := by
    rw [overlapCompletionWords_eq_hard_union_soft C]
    exact Finset.mem_union.mpr (Or.inr
      (Finset.mem_inter.mp hsoft).2)
  have htwo : (completionFibre C word).card = 2 :=
    (mem_overlapCompletionWords C word).1 hoverlap
  omega

/-- The exact global U-cardinality budget is the sum of genuinely
disjoint singleton-shell and soft-shell masses. -/
theorem strict_shell_global_card_eq_singleton_add_soft
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ) :
    (netStrictRigidUnusedLowerWords C exponent).card =
      (strictShellSingletonWords C exponent).card +
        (strictShellSoftWords C exponent).card := by
  rw [strict_shell_global_singleton_soft_partition C exponent,
    Finset.card_union_of_disjoint
      (strict_shell_global_singleton_soft_disjoint C exponent)]

/-- Every possible forward/reverse bridge-soft collision lies in
the SOFT portion of the actual unused strict lower cubes. -/
theorem bridge_soft_subset_global_strict_shell_soft
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ) :
    forwardReverseBridgeSoftWords C exponent ⊆
      strictShellSoftWords C exponent := by
  classical
  intro word hw
  exact Finset.mem_inter.mpr
    ⟨bridge_soft_subset_unused_strict_lower_words C exponent hw,
      forwardReverseBridgeSoftWords_subset_soft C exponent hw⟩

/-- A sharper bridge bound with the singleton shell capacity
already deducted, WITHOUT counting any slot as a true Boolean hole. -/
theorem bridge_soft_add_strict_shell_singleton_le_unused
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ) :
    (forwardReverseBridgeSoftWords C exponent).card +
      (strictShellSingletonWords C exponent).card ≤
        (netStrictRigidUnusedLowerWords C exponent).card := by
  have hbridge : (forwardReverseBridgeSoftWords C exponent).card ≤
      (strictShellSoftWords C exponent).card :=
    Finset.card_le_card
      (bridge_soft_subset_global_strict_shell_soft C exponent)
  have htotal :=
    strict_shell_global_card_eq_singleton_add_soft C exponent
  omega

/-- Exact numerical sharpening of the former global bridge <=
strict descent gap bound, retaining the already-singleton
portion of the shell as a separate non-reusable deduction. -/
theorem bridge_soft_add_strict_shell_singleton_le_local_gaps
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexp : ∀ x, exponent x ≤ n)
    (honeLoss : ∀ x, (active C x).card ≤ n - exponent x + 1) :
    (forwardReverseBridgeSoftWords C exponent).card +
      (strictShellSingletonWords C exponent).card ≤
        ∑ q ∈ netStrictDescentRigidCarriers C exponent,
          (2 ^ exponent q.1 - 2 ^ exponent q.2) := by
  have h :=
    bridge_soft_add_strict_shell_singleton_le_unused C exponent
  rw [unused_strict_lower_words_card_eq_sum_target_gaps
    C exponent hexp honeLoss] at h
  exact h

/-- Globally identify the ENTIRE soft portion of strict unused lower
capacity as the sum of oriented complete outgoing soft carrier faces.
The outer carrier decomposition is disjoint by strict lower cubes. -/
theorem strict_shell_global_soft_mass_eq_oriented_carrier_sum
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ) :
    (strictShellSoftWords C exponent).card =
      ∑ q ∈ netStrictDescentRigidCarriers C exponent,
        ∑ r ∈ strictShellOutgoingSoftCarriers C q,
          2 ^ (commonRetainedInactive C r.1 r.2).card := by
  classical
  have hunion :
      strictShellSoftWords C exponent =
      (netStrictDescentRigidCarriers C exponent).biUnion
        (fun q =>
          (retainedCompletionWords C q.1 \
              retainedCompletionWords C q.2) ∩
            softOverlapCompletionWords C) := by
    ext word
    constructor
    · intro hw
      have hunused := (Finset.mem_inter.mp hw).1
      have hsoft := (Finset.mem_inter.mp hw).2
      rw [unused_strict_lower_words_eq_union_shells] at hunused
      obtain ⟨q, hq, hqw⟩ := Finset.mem_biUnion.mp hunused
      exact Finset.mem_biUnion.mpr
        ⟨q, hq, Finset.mem_inter.mpr ⟨hqw, hsoft⟩⟩
    · intro hw
      obtain ⟨q, hq, hqw⟩ := Finset.mem_biUnion.mp hw
      apply Finset.mem_inter.mpr
      constructor
      · rw [unused_strict_lower_words_eq_union_shells]
        exact Finset.mem_biUnion.mpr
          ⟨q, hq, (Finset.mem_inter.mp hqw).1⟩
      · exact (Finset.mem_inter.mp hqw).2
  rw [hunion]
  have hpair :
      (((netStrictDescentRigidCarriers C exponent :
          Finset (V × V)) : Set (V × V))).PairwiseDisjoint
        (fun q =>
          (retainedCompletionWords C q.1 \
              retainedCompletionWords C q.2) ∩
            softOverlapCompletionWords C) := by
    intro q hq r hr hne
    apply Finset.disjoint_left.mpr
    intro word hqw hrw
    have hdisj :=
      strict_rigid_lower_shells_pairwiseDisjoint C exponent
        hq hr hne
    exact (Finset.disjoint_left.mp hdisj)
      (Finset.mem_inter.mp hqw).1
      (Finset.mem_inter.mp hrw).1
  rw [Finset.card_biUnion hpair]
  apply Finset.sum_congr rfl
  intro q hq
  exact strict_shell_soft_card_eq_outgoing_dyadic_sum
    C exponent hq

/-- Global exact conservation ledger: strictly lower rigid shell
dimensions split into globally owned singleton and outgoing soft mass,
without using either covered word class as genuine Boolean holes. -/
theorem strict_shell_global_singleton_add_oriented_soft_eq_local_gaps
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexp : ∀ x, exponent x ≤ n)
    (honeLoss : ∀ x, (active C x).card ≤ n - exponent x + 1) :
    (strictShellSingletonWords C exponent).card +
      (∑ q ∈ netStrictDescentRigidCarriers C exponent,
        ∑ r ∈ strictShellOutgoingSoftCarriers C q,
          2 ^ (commonRetainedInactive C r.1 r.2).card) =
      ∑ q ∈ netStrictDescentRigidCarriers C exponent,
        (2 ^ exponent q.1 - 2 ^ exponent q.2) := by
  have hcard :=
    strict_shell_global_card_eq_singleton_add_soft C exponent
  have hmass :=
    strict_shell_global_soft_mass_eq_oriented_carrier_sum C exponent
  have hgap :=
    unused_strict_lower_words_card_eq_sum_target_gaps
      C exponent hexp honeLoss
  omega


/-- SOFT-covered shell words that CANNOT participate even in the
candidate oriented forward/reverse bridge pool. -/
noncomputable def strictShellNonBridgeSoftWords
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ) : Finset (Fin n → Bool) :=
  strictShellSoftWords C exponent \
    forwardReverseBridgeSoftWords C exponent

/-- Exact—not just upper-bounded—division of the global soft shell
mass into potential bridge collisions and non-bridge soft words. -/
theorem strict_shell_soft_mass_eq_bridge_add_nonbridge
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ) :
    (strictShellSoftWords C exponent).card =
      (forwardReverseBridgeSoftWords C exponent).card +
        (strictShellNonBridgeSoftWords C exponent).card := by
  classical
  have hsubset :=
    bridge_soft_subset_global_strict_shell_soft C exponent
  have hcard :=
    Finset.card_sdiff_of_subset hsubset
  change (strictShellNonBridgeSoftWords C exponent).card =
      (strictShellSoftWords C exponent).card -
        (forwardReverseBridgeSoftWords C exponent).card at hcard
  have hle := Finset.card_le_card hsubset
  omega

/-- The nonbridge soft remainder has no word in common with
the potential bridge pool. This is a literal Finset reservation. -/
theorem strict_shell_nonbridge_disjoint_bridge
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ) :
    Disjoint (strictShellNonBridgeSoftWords C exponent)
      (forwardReverseBridgeSoftWords C exponent) := by
  classical
  apply Finset.disjoint_left.mpr
  intro word hw hn
  exact (Finset.mem_sdiff.mp hw).2 hn

/-- THREE-WAY exact globally non-reusing strict descent ledger.
The potential bridge pool is only the THIRD use category of
strict lower shells, beside singleton and nonbridge-soft mass.
No category is a genuine Boolean hole or unreserved surplus. -/
theorem strict_shell_singleton_bridge_nonbridge_eq_local_gaps
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexp : ∀ x, exponent x ≤ n)
    (honeLoss : ∀ x, (active C x).card ≤ n - exponent x + 1) :
    (strictShellSingletonWords C exponent).card +
      (forwardReverseBridgeSoftWords C exponent).card +
        (strictShellNonBridgeSoftWords C exponent).card =
      ∑ q ∈ netStrictDescentRigidCarriers C exponent,
        (2 ^ exponent q.1 - 2 ^ exponent q.2) := by
  have hpartition :=
    strict_shell_global_card_eq_singleton_add_soft C exponent
  have hbridge :=
    strict_shell_soft_mass_eq_bridge_add_nonbridge C exponent
  have hgap :=
    unused_strict_lower_words_card_eq_sum_target_gaps
      C exponent hexp honeLoss
  omega

#print axioms strict_shell_global_singleton_soft_partition
#print axioms strict_shell_soft_mass_eq_bridge_add_nonbridge
#print axioms strict_shell_nonbridge_disjoint_bridge
#print axioms strict_shell_singleton_bridge_nonbridge_eq_local_gaps
#print axioms strict_shell_global_singleton_soft_disjoint
#print axioms strict_shell_global_card_eq_singleton_add_soft
#print axioms bridge_soft_subset_global_strict_shell_soft
#print axioms bridge_soft_add_strict_shell_singleton_le_unused
#print axioms bridge_soft_add_strict_shell_singleton_le_local_gaps
#print axioms strict_shell_global_soft_mass_eq_oriented_carrier_sum
#print axioms strict_shell_global_singleton_add_oriented_soft_eq_local_gaps

end OrderedEdgeColoring
end JSP000404Research
