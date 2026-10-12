import JSP000404Research.ResidualTerminalStrictReverseGlobalInjection
import Mathlib.Tactic

/-!
# True final rigid obstruction = TWIN faces plus reversible strict descent

Using the previously proved one-layer endpoint budgets, every terminal
rigid carrier has nonincreasing target exponent. Partition it into:

* strict-descent rigid: upper exponent < lower exponent.
  The FULL hard face now admits a globally injective REVERSE safe flip
  into covered singleton/soft words.
* twin rigid: upper exponent = lower exponent.
  Its endpoints have IDENTICAL retained completion cubes, incoming
  retained colours, and outgoing retained colours. Such a face
  cannot be moved by the established strict-descent reverse mechanism.

The two carrier families and their corresponding Boolean faces
partition the entire terminal rigid remainder EXACTLY and disjointly.

This isolates the unique genuinely non-transportable rigid type.
It does not give true Boolean holes, nor claim that the forward
transport and reverse strict-descent sinks are mutually disjoint.
-/

namespace JSP000404Research
namespace OrderedEdgeColoring

noncomputable def netTwinRigidCarriers
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ) : Finset (V × V) := by
  classical
  exact (netRigidHardCarriers C exponent).filter
    (fun p => exponent p.1 = exponent p.2)

@[simp] theorem mem_netTwinRigidCarriers
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ) (p : V × V) :
    p ∈ netTwinRigidCarriers C exponent ↔
      p ∈ netRigidHardCarriers C exponent ∧
      exponent p.1 = exponent p.2 := by
  classical
  simp [netTwinRigidCarriers]

noncomputable def netTwinRigidWords
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ) : Finset (Fin n → Bool) :=
  (netTwinRigidCarriers C exponent).biUnion
    (carrierOverlapWords C)

/-- In the actual one-layer budget, all terminal rigid carriers
are EITHER strict exponent descent OR equal-exponent full twins. -/
theorem netRigidHardCarriers_eq_strict_union_twin_of_oneLayer
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexp : ∀ x, exponent x ≤ n)
    (honeLoss : ∀ x, (active C x).card ≤ n - exponent x + 1) :
    netRigidHardCarriers C exponent =
      netStrictDescentRigidCarriers C exponent ∪
        netTwinRigidCarriers C exponent := by
  classical
  ext p
  simp only [Finset.mem_union, mem_netStrictDescentRigidCarriers,
    mem_netTwinRigidCarriers]
  constructor
  · intro hp
    rcases netRigidHardCarrier_twin_cubes_or_strict_target_descent
      C exponent hexp honeLoss hp with htwin | hstrict
    · exact Or.inr ⟨hp,htwin.1⟩
    · exact Or.inl ⟨hp,hstrict⟩
  · rintro (⟨hp,_⟩ | ⟨hp,_⟩) <;> exact hp

/-- The terminal rigid Boolean-word remainder is exactly the
disjoint union of reverse-mobile strict faces and immobile twins. -/
theorem netRigidHardWords_eq_strict_union_twin_of_oneLayer
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexp : ∀ x, exponent x ≤ n)
    (honeLoss : ∀ x, (active C x).card ≤ n - exponent x + 1) :
    netRigidHardWords C exponent =
      netStrictDescentRigidWords C exponent ∪
        netTwinRigidWords C exponent := by
  classical
  unfold netRigidHardWords netStrictDescentRigidWords netTwinRigidWords
  rw [netRigidHardCarriers_eq_strict_union_twin_of_oneLayer
    C exponent hexp honeLoss]
  ext word
  simp only [Finset.mem_biUnion, Finset.mem_union]
  constructor
  · rintro ⟨p,hp | hp,hw⟩
    · exact Or.inl ⟨p,hp,hw⟩
    · exact Or.inr ⟨p,hp,hw⟩
  · rintro (⟨p,hp,hw⟩ | ⟨p,hp,hw⟩)
    · exact ⟨p,Or.inl hp,hw⟩
    · exact ⟨p,Or.inr hp,hw⟩

/-- Strict mobile and twin immobile terminal words cannot
overlap, because one Boolean word has one hard ordered carrier. -/
theorem net_strict_twin_rigid_words_disjoint
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ) :
    Disjoint (netStrictDescentRigidWords C exponent)
      (netTwinRigidWords C exponent) := by
  classical
  apply Finset.disjoint_left.mpr
  intro word hstr htw
  obtain ⟨p,hp,hpw⟩ := Finset.mem_biUnion.mp hstr
  obtain ⟨q,hq,hqw⟩ := Finset.mem_biUnion.mp htw
  have hpData := (mem_netStrictDescentRigidCarriers
    C exponent p).1 hp
  have hqData := (mem_netTwinRigidCarriers C exponent q).1 hq
  have hpHard :=
    ((mem_netUnpaidHardCarrierPairs C exponent p).1
      ((mem_netRigidHardCarriers C exponent p).1 hpData.1).1).1
  have hqHard :=
    ((mem_netUnpaidHardCarrierPairs C exponent q).1
      ((mem_netRigidHardCarriers C exponent q).1 hqData.1).1).1
  have hpq := hard_carrier_word_owner_unique
    C hpHard hqHard hpw hqw
  have hEq : exponent p.1 = exponent p.2 := by
    simpa only [hpq] using hqData.2
  omega

theorem netRigidHardWords_card_eq_strict_add_twin_of_oneLayer
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexp : ∀ x, exponent x ≤ n)
    (honeLoss : ∀ x, (active C x).card ≤ n - exponent x + 1) :
    (netRigidHardWords C exponent).card =
      (netStrictDescentRigidWords C exponent).card +
        (netTwinRigidWords C exponent).card := by
  rw [netRigidHardWords_eq_strict_union_twin_of_oneLayer
    C exponent hexp honeLoss]
  exact Finset.card_union_of_disjoint
    (net_strict_twin_rigid_words_disjoint C exponent)

/-- A full terminal TWIN hard face still carries exactly
the upper (equivalently lower) target exponent's dyadic mass. -/
theorem netTwinRigidWords_card_eq_dyadic_target_sum
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexp : ∀ x, exponent x ≤ n)
    (honeLoss : ∀ x, (active C x).card ≤ n - exponent x + 1) :
    (netTwinRigidWords C exponent).card =
      ∑ p ∈ netTwinRigidCarriers C exponent,
        2 ^ exponent p.2 := by
  classical
  have hpair :
      ((netTwinRigidCarriers C exponent : Finset (V × V)) :
        Set (V × V)).PairwiseDisjoint (carrierOverlapWords C) := by
    intro p hp q hq hpq
    apply carrierOverlapWords_pairwiseDisjoint C
    · have hpn := ((mem_netTwinRigidCarriers C exponent p).1
        (by simpa using hp)).1
      exact ((mem_overlapCarrierPairs C p).1
        ((mem_hardOverlapCarrierPairs C p).1
          ((mem_netUnpaidHardCarrierPairs C exponent p).1
            ((mem_netRigidHardCarriers C exponent p).1 hpn).1).1).1).1
    · have hqn := ((mem_netTwinRigidCarriers C exponent q).1
        (by simpa using hq)).1
      exact ((mem_overlapCarrierPairs C q).1
        ((mem_hardOverlapCarrierPairs C q).1
          ((mem_netUnpaidHardCarrierPairs C exponent q).1
            ((mem_netRigidHardCarriers C exponent q).1 hqn).1).1).1).1
    · exact hpq
  unfold netTwinRigidWords
  rw [Finset.card_biUnion hpair]
  apply Finset.sum_congr rfl
  intro p hp
  have hpn := ((mem_netTwinRigidCarriers C exponent p).1 hp).1
  have hpNet :=
    ((mem_netRigidHardCarriers C exponent p).1 hpn).1
  have hpData := (mem_netUnpaidHardCarrierPairs C exponent p).1 hpNet
  have hrig : p ∈ rigidHardOverlapCarrierPairs C :=
    (mem_rigidHardOverlapCarrierPairs C p).2
      ⟨hpData.1,((mem_netRigidHardCarriers C exponent p).1 hpn).2⟩
  have hb :=
    netRigidHardCarriers_endpoint_budgets_of_oneLayer
      C exponent hexp honeLoss p hpn
  exact (terminal_rigid_carrier_mass_and_zero_surplus_without_word
    C exponent hrig hpData.2.1 hpData.2.2.1 hpData.2.2.2
      hb.1 hb.2).1

/-- A full exact THREE-WAY partition of genuinely still-unpaid
hard Boolean words: outgoing transport, reverse strict descent,
or exactly twin completion cubes. -/
theorem remainingUnpaidHard_card_eq_transport_strict_twin
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexp : ∀ x, exponent x ≤ n)
    (honeLoss : ∀ x, (active C x).card ≤ n - exponent x + 1) :
    (remainingUnpaidHardAfterMixedRigidWords C exponent).card =
      (netTransportableHardWords C exponent).card +
      (netStrictDescentRigidWords C exponent).card +
      (netTwinRigidWords C exponent).card := by
  rw [remainingUnpaidHard_card_eq_transportable_add_rigid,
    netRigidHardWords_card_eq_strict_add_twin_of_oneLayer
      C exponent hexp honeLoss]
  omega

#print axioms netRigidHardCarriers_eq_strict_union_twin_of_oneLayer
#print axioms netRigidHardWords_card_eq_strict_add_twin_of_oneLayer
#print axioms netTwinRigidWords_card_eq_dyadic_target_sum
#print axioms remainingUnpaidHard_card_eq_transport_strict_twin

end OrderedEdgeColoring
end JSP000404Research
