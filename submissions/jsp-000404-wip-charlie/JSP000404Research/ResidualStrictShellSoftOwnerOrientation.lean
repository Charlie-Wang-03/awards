import JSP000404Research.ResidualStrictRigidLowerShellDecomposition
import Mathlib.Tactic

/-!
# Orientation of SOFT overlap in strict-rigid lower shells

A strict rigid carrier q=(a,v) has lower shell Q_a \ Q_v.
Previous work showed these shells are disjoint and contain only
singleton-covered or SOFT-overlapped Boolean words, never hard words.

A stronger geometric combinatorial constraint holds: if a word in
Q_a \ Q_v is SOFT overlapped by a residual carrier r=(b,z),
then b=a. Indeed the word belongs to both residual LOWER cubes
Q_a and Q_b, so residual-lower-cube uniqueness forces b=a.

Moreover z differs from v, since q is hard but r is soft. Thus all
soft completions in the shell are oriented residual edges OUTGOING
from the lower endpoint of their strict rigid carrier. This does
not assume planar AngleCap, produce true holes, or prove payment.
-/

namespace JSP000404Research
namespace OrderedEdgeColoring

/-- A soft word in a strict lower shell has its unique residual
SOFT owner starting at the lower endpoint of the strict rigid pair. -/
theorem strict_shell_soft_carrier_lower_eq
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    {q r : V × V} {word : Fin n → Bool}
    (hq : q ∈ netStrictDescentRigidCarriers C exponent)
    (hr : r ∈ softOverlapCarrierPairs C)
    (hshell : word ∈ retainedCompletionWords C q.1 \
        retainedCompletionWords C q.2)
    (hsoft : word ∈ carrierOverlapWords C r) :
    r.1 = q.1 := by
  have hqNet := ((mem_netStrictDescentRigidCarriers C exponent q).1 hq).1
  have hqRigid := (mem_netRigidHardCarriers C exponent q).1 hqNet
  have hqHard :=
    ((mem_netUnpaidHardCarrierPairs C exponent q).1 hqRigid.1).1
  have hqRes : q.1 < q.2 ∧ IsResidual C q.1 q.2 :=
    (mem_residualCarrierPairs C q.1 q.2).1
      ((mem_overlapCarrierPairs C q).1
        ((mem_hardOverlapCarrierPairs C q).1 hqHard).1).1
  have hrRes : r.1 < r.2 ∧ IsResidual C r.1 r.2 :=
    (mem_residualCarrierPairs C r.1 r.2).1
      ((mem_overlapCarrierPairs C r).1
        ((mem_softOverlapCarrierPairs C r).1 hr).1).1
  have hwordr : word ∈ retainedCompletionWords C r.1 ∩
      retainedCompletionWords C r.2 := hsoft
  have heq : q.1 = r.1 :=
    residual_lower_completion_word_unique C
      hqRes.1 hrRes.1 hqRes.2 hrRes.2
      (Finset.mem_sdiff.mp hshell).1
      (Finset.mem_inter.mp hwordr).1
  exact heq.symm

/-- The soft owner cannot end at the same upper endpoint as the hard
strict-rigid carrier. Otherwise the ordered pairs coincide, while
one carrier is hard and the other soft. -/
theorem strict_shell_soft_carrier_upper_ne
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    {q r : V × V} {word : Fin n → Bool}
    (hq : q ∈ netStrictDescentRigidCarriers C exponent)
    (hr : r ∈ softOverlapCarrierPairs C)
    (hshell : word ∈ retainedCompletionWords C q.1 \
        retainedCompletionWords C q.2)
    (hsoft : word ∈ carrierOverlapWords C r) :
    r.2 ≠ q.2 := by
  have hlow := strict_shell_soft_carrier_lower_eq
    C exponent hq hr hshell hsoft
  have hqNet := ((mem_netStrictDescentRigidCarriers C exponent q).1 hq).1
  have hqRigid := (mem_netRigidHardCarriers C exponent q).1 hqNet
  have hqHard :=
    ((mem_netUnpaidHardCarrierPairs C exponent q).1 hqRigid.1).1
  have hqSame : SameRetained C q.1 q.2 :=
    ((mem_hardOverlapCarrierPairs C q).1 hqHard).2
  have hrNot : ¬ SameRetained C r.1 r.2 :=
    ((mem_softOverlapCarrierPairs C r).1 hr).2
  intro hup
  have hrq : r = q := Prod.ext hlow hup
  rw [hrq] at hrNot
  exact hrNot hqSame

/-- Every SOFT word in a strict lower shell has an oriented
residual partner strictly above the lower endpoint and distinct
from the strict hard upper endpoint. -/
theorem strict_shell_soft_word_has_distinct_upper_partner
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    {q : V × V} {word : Fin n → Bool}
    (hq : q ∈ netStrictDescentRigidCarriers C exponent)
    (hshell : word ∈ retainedCompletionWords C q.1 \
      retainedCompletionWords C q.2)
    (hwsoft : word ∈ softOverlapCompletionWords C) :
    ∃ r ∈ softOverlapCarrierPairs C,
      r.1 = q.1 ∧ r.2 ≠ q.2 ∧
      word ∈ carrierOverlapWords C r := by
  classical
  change word ∈ (softOverlapCarrierPairs C).biUnion
    (carrierOverlapWords C) at hwsoft
  obtain ⟨r, hr, hword⟩ := Finset.mem_biUnion.mp hwsoft
  exact ⟨r, hr,
    strict_shell_soft_carrier_lower_eq C exponent hq hr hshell hword,
    strict_shell_soft_carrier_upper_ne C exponent hq hr hshell hword,
    hword⟩

/-- Global localization: all SOFT-overlapped words in unused lower
capacity belong to an outgoing soft carrier sharing its lower
endpoint with one strict-descent rigid carrier. The strict carrier
also uniquely owns the containing lower shell. -/
theorem unused_strict_lower_soft_has_oriented_owner
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    {word : Fin n → Bool}
    (hunused : word ∈ netStrictRigidUnusedLowerWords C exponent)
    (hwsoft : word ∈ softOverlapCompletionWords C) :
    ∃ q ∈ netStrictDescentRigidCarriers C exponent,
      ∃ r ∈ softOverlapCarrierPairs C,
        word ∈ retainedCompletionWords C q.1 \
          retainedCompletionWords C q.2 ∧
        r.1 = q.1 ∧ r.2 ≠ q.2 ∧
        word ∈ carrierOverlapWords C r := by
  classical
  rw [unused_strict_lower_words_eq_union_shells] at hunused
  obtain ⟨q, hq, hshell⟩ := Finset.mem_biUnion.mp hunused
  obtain ⟨r, hr, hlow, hup, hword⟩ :=
    strict_shell_soft_word_has_distinct_upper_partner
      C exponent hq hshell hwsoft
  exact ⟨q, hq, r, hr, hshell, hlow, hup, hword⟩

#print axioms strict_shell_soft_carrier_lower_eq
#print axioms strict_shell_soft_carrier_upper_ne
#print axioms strict_shell_soft_word_has_distinct_upper_partner
#print axioms unused_strict_lower_soft_has_oriented_owner

end OrderedEdgeColoring
end JSP000404Research
