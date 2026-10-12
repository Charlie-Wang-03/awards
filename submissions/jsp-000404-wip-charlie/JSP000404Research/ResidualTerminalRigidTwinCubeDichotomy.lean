import JSP000404Research.ResidualTerminalHardNetPaymentReduction
import Mathlib.Tactic

/-!
# Terminal rigid carriers: exact twin cubes or strict target descent

A no-outward-transport hard carrier has the upper completion cube
contained in the lower. If the endpoints are both projected-budget
saturated and their target exponents are EQUAL, the cubes necessarily
have the SAME cardinality and hence coincide exactly.

If the two target exponents are not equal, the upper exponent strictly
decreases. The two terminal branches therefore are:
  - rigid TWIN complete Boolean cubes (equal target exponent); or
  - rigid STRICT target-weight descent (upper smaller than lower).

This is a genuine geometric/combinatorial obstruction refinement,
without any Hall or true-hole payment assumption.
-/

namespace JSP000404Research
namespace OrderedEdgeColoring

/-- Equal projected free dimensions make a hard nested rigid
completion pair literally EQUAL Boolean cubes. -/
theorem rigid_hard_equal_projectedFree_twin_completion_cubes
    {V : Type*} [LinearOrder V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    {a v : V}
    (hsame : SameRetained C a v)
    (hno : ¬ HasOutgoingHardTransport C a v)
    (hfree : projectedFree C a = projectedFree C v) :
    retainedCompletionWords C a = retainedCompletionWords C v := by
  classical
  have hsub := hard_no_transport_upper_cube_subset_lower C hsame hno
  have hcard :
      (retainedCompletionWords C a).card ≤
        (retainedCompletionWords C v).card := by
    rw [retainedCompletionWords_card C a,
      retainedCompletionWords_card C v, hfree]
  exact (Finset.eq_of_subset_of_card_le hsub hcard).symm

/-- On a rigid hard pair, equality of the two projected budgets
also forces equality of their retained-active coordinate supports. -/
theorem rigid_hard_equal_projectedFree_twin_retainedActive
    {V : Type*} [LinearOrder V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    {a v : V}
    (hsame : SameRetained C a v)
    (hno : ¬ HasOutgoingHardTransport C a v)
    (hfree : projectedFree C a = projectedFree C v) :
    retainedActive C a = retainedActive C v := by
  classical
  have hsub := hard_no_transport_retainedActive_subset C hsame hno
  have hboundA : (retainedActive C a).card ≤ n := by
    simpa using Finset.card_le_univ (retainedActive C a)
  have hboundV : (retainedActive C v).card ≤ n := by
    simpa using Finset.card_le_univ (retainedActive C v)
  have hcard :
      (retainedActive C v).card ≤
        (retainedActive C a).card := by
    unfold projectedFree at hfree
    omega
  exact Finset.eq_of_subset_of_card_le hsub hcard

/-- Terminal rigid carriers necessarily have twin completion
cubes or STRICT exponent descent. This is a CARRIER-level
assertion, not a statement about an arbitrarily selected word. -/
theorem netRigidHardCarrier_twin_cubes_or_strict_target_descent
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexp : ∀ x, exponent x ≤ n)
    (honeLoss : ∀ x, (active C x).card ≤ n - exponent x + 1)
    {p : V × V}
    (hp : p ∈ netRigidHardCarriers C exponent) :
    (exponent p.1 = exponent p.2 ∧
       retainedCompletionWords C p.1 = retainedCompletionWords C p.2 ∧
       retainedActive C p.1 = retainedActive C p.2)
    ∨
      exponent p.2 < exponent p.1 := by
  have hpdata := (mem_netRigidHardCarriers C exponent p).1 hp
  have hnet := (mem_netUnpaidHardCarrierPairs C exponent p).1 hpdata.1
  have hrigid : p ∈ rigidHardOverlapCarrierPairs C :=
    (mem_rigidHardOverlapCarrierPairs C p).2 ⟨hnet.1, hpdata.2⟩
  have hbudget :=
    netRigidHardCarriers_endpoint_budgets_of_oneLayer
      C exponent hexp honeLoss p hp
  have hterminal :=
    terminal_rigid_carrier_mass_and_zero_surplus_without_word
      C exponent hrigid hnet.2.1 hnet.2.2.1 hnet.2.2.2
        hbudget.1 hbudget.2
  have hrig := (mem_rigidHardOverlapCarrierPairs C p).1 hrigid
  have hsame := ((mem_hardOverlapCarrierPairs C p).1 hrig.1).2
  by_cases heq : exponent p.1 = exponent p.2
  · left
    have hfree : projectedFree C p.1 = projectedFree C p.2 := by
      have hsat :=
        terminal_rigid_carrier_both_saturated_without_word
          C exponent hrigid hnet.2.1 hnet.2.2.1 hnet.2.2.2
          hbudget.1 hbudget.2
      omega
    exact ⟨heq,
      rigid_hard_equal_projectedFree_twin_completion_cubes
        C hsame hrig.2 hfree,
      rigid_hard_equal_projectedFree_twin_retainedActive
        C hsame hrig.2 hfree⟩
  · right
    omega

#print axioms rigid_hard_equal_projectedFree_twin_completion_cubes
#print axioms rigid_hard_equal_projectedFree_twin_retainedActive
#print axioms netRigidHardCarrier_twin_cubes_or_strict_target_descent

end OrderedEdgeColoring
end JSP000404Research
