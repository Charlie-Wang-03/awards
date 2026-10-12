import JSP000404Research.ResidualStrictShellSoftOwnerOrientation
import Mathlib.Tactic

/-!
# Exact oriented soft-overlap mass ledger inside each strict-rigid shell

For each strict rigid carrier q=(a,v), the shell Q_a \ Q_v consists
exactly of singleton words and overlaps on SOFT residual carriers
(a,z), z != v. Moreover a soft carrier (a,z) contributes its ENTIRE
face Q_a ∩ Q_z to the shell: the two upper residual completion cubes
Q_z and Q_v are disjoint.

This yields an exact local equality (under one-layer saturation):

  2^k(a) - 2^k(v)
    = singleton-in-shell mass
      + SUM_(soft r with r.lower=a) 2^commonInactive(r).

The singleton and soft terms are still COVERED words. This ledger
neither proves global hole/surplus payment nor removes the admitted WIP.
-/

namespace JSP000404Research
namespace OrderedEdgeColoring

noncomputable def strictShellOutgoingSoftCarriers
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (q : V × V) : Finset (V × V) :=
  (softOverlapCarrierPairs C).filter (fun r => r.1 = q.1)

@[simp] theorem mem_strictShellOutgoingSoftCarriers
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (q r : V × V) :
    r ∈ strictShellOutgoingSoftCarriers C q ↔
      r ∈ softOverlapCarrierPairs C ∧ r.1 = q.1 := by
  classical
  simp [strictShellOutgoingSoftCarriers]

/-- A soft residual carrier cannot share both endpoints with a strict
hard carrier, even though they may share the lower endpoint. -/
theorem strict_outgoing_soft_upper_ne
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    {q r : V × V}
    (hq : q ∈ netStrictDescentRigidCarriers C exponent)
    (hr : r ∈ softOverlapCarrierPairs C)
    (hlow : r.1 = q.1) : r.2 ≠ q.2 := by
  have hnet := ((mem_netStrictDescentRigidCarriers C exponent q).1 hq).1
  have hrigid := (mem_netRigidHardCarriers C exponent q).1 hnet
  have hhard :=
    ((mem_netUnpaidHardCarrierPairs C exponent q).1 hrigid.1).1
  have hqSame : SameRetained C q.1 q.2 :=
    ((mem_hardOverlapCarrierPairs C q).1 hhard).2
  have hrNot : ¬ SameRetained C r.1 r.2 :=
    ((mem_softOverlapCarrierPairs C r).1 hr).2
  intro hup
  have hrq : r = q := Prod.ext hlow hup
  rw [hrq] at hrNot
  exact hrNot hqSame

/-- Every word of an outgoing SOFT carrier's full overlap face lies
in the strict lower shell. The upper completion cubes are disjoint
because both upper vertices receive residual edges, and differ. -/
theorem strict_outgoing_soft_full_face_subset_shell
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    {q r : V × V}
    (hq : q ∈ netStrictDescentRigidCarriers C exponent)
    (hr : r ∈ strictShellOutgoingSoftCarriers C q) :
    carrierOverlapWords C r ⊆
      retainedCompletionWords C q.1 \
        retainedCompletionWords C q.2 := by
  classical
  have hrs := (mem_strictShellOutgoingSoftCarriers C q r).1 hr
  have hnet := ((mem_netStrictDescentRigidCarriers C exponent q).1 hq).1
  have hrigid := (mem_netRigidHardCarriers C exponent q).1 hnet
  have hhard :=
    ((mem_netUnpaidHardCarrierPairs C exponent q).1 hrigid.1).1
  have hqRes : q.1 < q.2 ∧ IsResidual C q.1 q.2 :=
    (mem_residualCarrierPairs C q.1 q.2).1
      ((mem_overlapCarrierPairs C q).1
        ((mem_hardOverlapCarrierPairs C q).1 hhard).1).1
  have hrRes : r.1 < r.2 ∧ IsResidual C r.1 r.2 :=
    (mem_residualCarrierPairs C r.1 r.2).1
      ((mem_overlapCarrierPairs C r).1
        ((mem_softOverlapCarrierPairs C r).1 hrs.1).1).1
  have hne : r.2 ≠ q.2 :=
    strict_outgoing_soft_upper_ne C exponent hq hrs.1 hrs.2
  have hd : Disjoint
      (retainedCompletionWords C r.2)
      (retainedCompletionWords C q.2) :=
    residual_upper_completion_cubes_disjoint C
      hrRes.1 hqRes.1 hrRes.2 hqRes.2 hne
  intro word hw
  have hw' : word ∈ retainedCompletionWords C r.1 ∩
    retainedCompletionWords C r.2 := hw
  apply Finset.mem_sdiff.mpr
  constructor
  · simpa only [hrs.2] using (Finset.mem_inter.mp hw').1
  · exact (Finset.disjoint_left.mp hd) (Finset.mem_inter.mp hw').2

/-- Soft mass in a fixed shell is EXACTLY the union of full overlap
faces of outgoing soft residual carriers with the same lower vertex. -/
theorem strict_shell_soft_words_eq_outgoing_faces
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    {q : V × V}
    (hq : q ∈ netStrictDescentRigidCarriers C exponent) :
    (retainedCompletionWords C q.1 \
        retainedCompletionWords C q.2) ∩
      softOverlapCompletionWords C =
      (strictShellOutgoingSoftCarriers C q).biUnion
        (carrierOverlapWords C) := by
  classical
  ext word
  constructor
  · intro hw
    have hshell := (Finset.mem_inter.mp hw).1
    have hwsoft := (Finset.mem_inter.mp hw).2
    obtain ⟨r, hr, hlow, _hne, hrword⟩ :=
      strict_shell_soft_word_has_distinct_upper_partner
        C exponent hq hshell hwsoft
    exact Finset.mem_biUnion.mpr
      ⟨r, (mem_strictShellOutgoingSoftCarriers C q r).2
        ⟨hr, hlow⟩, hrword⟩
  · intro hw
    obtain ⟨r, hr, hrword⟩ := Finset.mem_biUnion.mp hw
    apply Finset.mem_inter.mpr
    constructor
    · exact strict_outgoing_soft_full_face_subset_shell
        C exponent hq hr hrword
    · change word ∈ (softOverlapCarrierPairs C).biUnion
        (carrierOverlapWords C)
      exact Finset.mem_biUnion.mpr
        ⟨r, ((mem_strictShellOutgoingSoftCarriers C q r).1 hr).1,
          hrword⟩

/-- Exact dyadic mass, rather than a mere inclusion, of all outgoing
SOFT residual overlaps in one strict-rigid lower shell. -/
theorem strict_shell_soft_card_eq_outgoing_dyadic_sum
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    {q : V × V}
    (hq : q ∈ netStrictDescentRigidCarriers C exponent) :
    ((retainedCompletionWords C q.1 \
        retainedCompletionWords C q.2) ∩
      softOverlapCompletionWords C).card =
      ∑ r ∈ strictShellOutgoingSoftCarriers C q,
        2 ^ (commonRetainedInactive C r.1 r.2).card := by
  classical
  rw [strict_shell_soft_words_eq_outgoing_faces C exponent hq]
  have hpair :
      (((strictShellOutgoingSoftCarriers C q : Finset (V × V)) :
        Set (V × V))).PairwiseDisjoint
          (carrierOverlapWords C) := by
    intro r hr s hs hrs
    apply overlapCarrierWords_pairwiseDisjoint C
    · exact ((mem_softOverlapCarrierPairs C r).1
        ((mem_strictShellOutgoingSoftCarriers C q r).1 hr).1).1
    · exact ((mem_softOverlapCarrierPairs C s).1
        ((mem_strictShellOutgoingSoftCarriers C q s).1 hs).1).1
    · exact hrs
  rw [Finset.card_biUnion hpair]
  apply Finset.sum_congr rfl
  intro r hr
  have hsoft := ((mem_strictShellOutgoingSoftCarriers C q r).1 hr).1
  obtain ⟨word, hw⟩ :=
    ((mem_overlapCarrierPairs C r).1
      ((mem_softOverlapCarrierPairs C r).1 hsoft).1).2
  have hp := (mem_carrierOverlapWords C r word).1 hw
  exact retainedCompletionWords_inter_card C hp.1 hp.2

/-- Exact local capacity ledger: strict rigid lower descent is made
of singleton-covered words plus full outgoing SOFT overlap faces.
The sources and targets of this identity are covered, not holes. -/
theorem strict_shell_singleton_add_outgoing_soft_mass_eq_target_gap
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexp : ∀ x, exponent x ≤ n)
    (honeLoss : ∀ x, (active C x).card ≤ n - exponent x + 1)
    {q : V × V}
    (hq : q ∈ netStrictDescentRigidCarriers C exponent) :
    ((retainedCompletionWords C q.1 \
        retainedCompletionWords C q.2) ∩
      singletonCompletionWords C).card +
      (∑ r ∈ strictShellOutgoingSoftCarriers C q,
        2 ^ (commonRetainedInactive C r.1 r.2).card) =
      2 ^ exponent q.1 - 2 ^ exponent q.2 := by
  classical
  let Q := retainedCompletionWords C q.1 \
    retainedCompletionWords C q.2
  let A := singletonCompletionWords C
  let B := softOverlapCompletionWords C
  have hsubset : Q ⊆ A ∪ B :=
    strict_rigid_lower_shell_subset_singleton_soft C exponent hq
  have hpart : Q = (Q ∩ A) ∪ (Q ∩ B) := by
    ext word
    constructor
    · intro hw
      rcases Finset.mem_union.mp (hsubset hw) with hA | hB
      · exact Finset.mem_union.mpr (Or.inl
          (Finset.mem_inter.mpr ⟨hw, hA⟩))
      · exact Finset.mem_union.mpr (Or.inr
          (Finset.mem_inter.mpr ⟨hw, hB⟩))
    · intro hw
      rcases Finset.mem_union.mp hw with hA | hB
      · exact (Finset.mem_inter.mp hA).1
      · exact (Finset.mem_inter.mp hB).1
  have hdisj : Disjoint (Q ∩ A) (Q ∩ B) := by
    apply Finset.disjoint_left.mpr
    intro word hA hB
    have hone : (completionFibre C word).card = 1 :=
      (mem_singletonCompletionWords C word).1
        (Finset.mem_inter.mp hA).2
    have hs : word ∈ softOverlapCompletionWords C :=
      (Finset.mem_inter.mp hB).2
    have htwo : (completionFibre C word).card = 2 := by
      apply (mem_overlapCompletionWords C word).1
      rw [overlapCompletionWords_eq_hard_union_soft C]
      exact Finset.mem_union.mpr (Or.inr hs)
    omega
  have hcard :
      (Q ∩ A).card + (Q ∩ B).card = Q.card := by
    calc
      (Q ∩ A).card + (Q ∩ B).card =
          ((Q ∩ A) ∪ (Q ∩ B)).card :=
        (Finset.card_union_of_disjoint hdisj).symm
      _ = Q.card := by rw [← hpart]
  change ((retainedCompletionWords C q.1 \
      retainedCompletionWords C q.2) ∩
      singletonCompletionWords C).card +
      (∑ r ∈ strictShellOutgoingSoftCarriers C q,
        2 ^ (commonRetainedInactive C r.1 r.2).card) = _
  rw [← strict_shell_soft_card_eq_outgoing_dyadic_sum
    C exponent hq]
  exact hcard.trans
    (strict_rigid_lower_shell_card_eq_target_gap
      C exponent hexp honeLoss hq)

#print axioms strict_outgoing_soft_upper_ne
#print axioms strict_outgoing_soft_full_face_subset_shell
#print axioms strict_shell_soft_words_eq_outgoing_faces
#print axioms strict_shell_soft_card_eq_outgoing_dyadic_sum
#print axioms strict_shell_singleton_add_outgoing_soft_mass_eq_target_gap

end OrderedEdgeColoring
end JSP000404Research
