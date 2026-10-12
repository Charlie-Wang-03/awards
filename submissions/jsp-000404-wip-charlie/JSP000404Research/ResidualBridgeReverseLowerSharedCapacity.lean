import JSP000404Research.ResidualForwardReverseBridgeDyadicMass
import Mathlib.Tactic

/-!
# Bridge-soft mass and reverse strict-rigid hard mass SHARE one lower cube

For every candidate oriented forward/reverse soft bridge (b,v), the
lower endpoint b is the lower vertex of a strict-descending terminal
rigid hard carrier (b,z). The whole bridge-soft overlap face Q_b ∩ Q_v
lies INSIDE the lower completion cube Q_b.

The original strict-rigid hard overlap face Q_b ∩ Q_z also lies
inside that same Q_b. The bridge face is SOFT; the rigid source is
HARD; hence these two types are COMPLETELY DISJOINT.

Consequently the ENTIRE candidate bridge-soft pool together with
ALL strict-rigid hard source words fit into the union of the lower
completion cubes of the strict-rigid carriers.

This is important: the bridge potential cross-collision pool and
the reverse hard source mass are NOT two independent budgets. The
same canonical lower completion cube must accommodate both.

The sum of the lower cube sizes is exactly
  SUM_(strict carrier (b,z)) 2 ^ exponent(b)
under the certified one-layer doubly saturated endpoint budget.

This does NOT claim that covered bridge words are true holes,
nor that the last global payment is proved.
-/

namespace JSP000404Research
namespace OrderedEdgeColoring

noncomputable def netStrictRigidLowerCapacityWords
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ) : Finset (Fin n → Bool) :=
  (netStrictDescentRigidCarriers C exponent).biUnion
    (fun q => retainedCompletionWords C q.1)

/-- All POTENTIAL forward/reverse bridge-soft words are located in
the LOWER completion cubes of strict-descending rigid carriers. -/
theorem forwardReverseBridgeSoftWords_subset_strict_lower_cubes
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ) :
    forwardReverseBridgeSoftWords C exponent ⊆
      netStrictRigidLowerCapacityWords C exponent := by
  classical
  intro w hw
  obtain ⟨r,hr,hrw⟩ := Finset.mem_biUnion.mp hw
  obtain ⟨hsoft,p,hp,q,hq,hlo,hhi⟩ :=
    Finset.mem_filter.mp hr
  have hwlo : w ∈ retainedCompletionWords C r.1 :=
    (Finset.mem_inter.mp hrw).1
  change w ∈ (netStrictDescentRigidCarriers C exponent).biUnion
    (fun q => retainedCompletionWords C q.1)
  exact Finset.mem_biUnion.mpr
    ⟨q,hq,by simpa only [hlo] using hwlo⟩

/-- Every reverse strict-rigid source hard word also belongs to
the same union of lower completion cubes. -/
theorem netStrictDescentRigidWords_subset_strict_lower_cubes
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ) :
    netStrictDescentRigidWords C exponent ⊆
      netStrictRigidLowerCapacityWords C exponent := by
  classical
  intro w hw
  obtain ⟨q,hq,hqw⟩ := Finset.mem_biUnion.mp hw
  change w ∈ (netStrictDescentRigidCarriers C exponent).biUnion
    (fun q => retainedCompletionWords C q.1)
  exact Finset.mem_biUnion.mpr
    ⟨q,hq,(Finset.mem_inter.mp hqw).1⟩

/-- Different origins: bridge = SOFT overlap and reverse rigid
source = HARD overlap. Their word sets can never intersect. -/
theorem forwardReverseBridgeSoftWords_disjoint_strict_rigid_words
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ) :
    Disjoint (forwardReverseBridgeSoftWords C exponent)
      (netStrictDescentRigidWords C exponent) := by
  classical
  apply Finset.disjoint_left.mpr
  intro w hwbridge hwrigid
  have hsoft : w ∈ softOverlapCompletionWords C :=
    forwardReverseBridgeSoftWords_subset_soft C exponent hwbridge
  obtain ⟨q,hq,hqw⟩ := Finset.mem_biUnion.mp hwrigid
  have hqnet := ((mem_netStrictDescentRigidCarriers C exponent q).1 hq).1
  have hqhard :=
    ((mem_netUnpaidHardCarrierPairs C exponent q).1
      ((mem_netRigidHardCarriers C exponent q).1 hqnet).1).1
  have hhard : w ∈ hardOverlapCompletionWords C :=
    Finset.mem_biUnion.mpr ⟨q,hqhard,hqw⟩
  exact Finset.disjoint_left.mp
    (hard_soft_overlap_words_disjoint C) hhard hsoft

/-- Joint source and candidate bridge pool, both embedded in
the same UNION of lower rigid source cubes. -/
theorem bridge_soft_union_reverse_strict_subset_lower_cubes
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ) :
    forwardReverseBridgeSoftWords C exponent ∪
        netStrictDescentRigidWords C exponent ⊆
      netStrictRigidLowerCapacityWords C exponent := by
  exact Finset.union_subset
    (forwardReverseBridgeSoftWords_subset_strict_lower_cubes C exponent)
    (netStrictDescentRigidWords_subset_strict_lower_cubes C exponent)

/-- No double charge: bridge-soft mass plus strict-rigid hard mass
fits into ONE collection of lower completion cubes. -/
theorem bridge_soft_add_reverse_strict_le_lower_cubes
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ) :
    (forwardReverseBridgeSoftWords C exponent).card +
      (netStrictDescentRigidWords C exponent).card ≤
        (netStrictRigidLowerCapacityWords C exponent).card := by
  have hsub :=
    Finset.card_le_card
      (bridge_soft_union_reverse_strict_subset_lower_cubes C exponent)
  rw [Finset.card_union_of_disjoint
    (forwardReverseBridgeSoftWords_disjoint_strict_rigid_words
      C exponent)] at hsub
  exact hsub

#print axioms forwardReverseBridgeSoftWords_subset_strict_lower_cubes
#print axioms netStrictDescentRigidWords_subset_strict_lower_cubes
#print axioms forwardReverseBridgeSoftWords_disjoint_strict_rigid_words
#print axioms bridge_soft_add_reverse_strict_le_lower_cubes

end OrderedEdgeColoring
end JSP000404Research
