import JSP000404Research.ResidualUnpaidRigidSaturation
import Mathlib.Tactic

/-!
# A genuine hole-free strict-profile capacity theorem

When every target exponent is STRICTLY below its projected free
dimension, every hard residual carrier belongs to the already
certified and globally surplus-paid matching. There is no profile
loss. Thus the only remaining possible debt is the SOFT-overlap mass.

If the soft-overlap mass is at most the number of genuine Boolean
holes, the sharp dyadic capacity follows, with NO use of the
already reserved surplus a second time.

The soft-versus-hole assumption is explicit and is NOT known for
all actual planar configurations. This is a restricted, non-admitted
theorem and does NOT discharge the planar lower-branch WIP.
-/

namespace JSP000404Research
namespace OrderedEdgeColoring

open scoped BigOperators

/-- Every hard carrier is surplus-payable if both endpoint profiles
are strictly slack; hence there are no unpaid hard Boolean words. -/
theorem unpaidHardOverlapWords_eq_empty_of_all_strict
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hstrict : ∀ v, exponent v < projectedFree C v) :
    unpaidHardOverlapWords C exponent = ∅ := by
  classical
  apply Finset.eq_empty_iff_forall_not_mem.mpr
  intro word hw
  obtain ⟨p, hcarrier, hnot, _⟩ :=
    unpaidHardWord_has_unpayable_hard_carrier C exponent hw
  apply hnot
  exact (mem_surplusPayableHardCarrierPairs C exponent p).2
    ⟨hcarrier, Or.inl ⟨hstrict p.1, hstrict p.2⟩⟩

/-- Strict projected slack at every vertex rules out all profile
losses, independently of planar geometry or the number of vertices. -/
theorem totalDyadicProfileLoss_eq_zero_of_all_strict
    {V : Type*} [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hstrict : ∀ v, exponent v < projectedFree C v) :
    totalDyadicProfileLoss exponent (projectedFree C) = 0 := by
  unfold totalDyadicProfileLoss
  apply Finset.sum_eq_zero
  intro v _
  have hpow : 2 ^ exponent v ≤ 2 ^ projectedFree C v :=
    Nat.pow_le_pow_right (by norm_num : (0 : ℕ) < 2)
      (Nat.le_of_lt (hstrict v))
  exact Nat.sub_eq_zero_of_le hpow

/-- Genuine n-bit capacity in the fully strict-profile regime
when SOFT Boolean overlap can be paid by TRUE ambient holes.

All hard overlap has been globally paid by pairwise-disjoint
surplus accounts; no projected profile loss remains. -/
theorem strict_profile_capacity_of_soft_overlap_le_holes
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hstrict : ∀ v, exponent v < projectedFree C v)
    (hsoft :
      (softOverlapCompletionWords C).card ≤
        2 ^ n - (coveredCompletionWords C).card) :
    (∑ v : V, 2 ^ exponent v) ≤ 2 ^ n := by
  have hhard :=
    unpaidHardOverlapWords_eq_empty_of_all_strict C exponent hstrict
  have hloss :=
    totalDyadicProfileLoss_eq_zero_of_all_strict C exponent hstrict
  have hpay :
      (softOverlapCompletionWords C).card +
        (unpaidHardOverlapWords C exponent).card +
        totalDyadicProfileLoss exponent (projectedFree C) ≤
      (2 ^ n - (coveredCompletionWords C).card) +
        (totalDyadicProfileSurplus exponent (projectedFree C) -
          (surplusPaidHardOverlapWords C exponent).card) := by
    rw [hhard, hloss]
    simp only [Finset.card_empty, add_zero]
    exact hsoft.trans (Nat.le_add_right _ _)
  apply exponent_capacity_of_completion_defect_payment C exponent
  exact (completion_defect_payment_iff_soft_and_unpaid_hard
    C exponent).2 hpay

#print axioms unpaidHardOverlapWords_eq_empty_of_all_strict
#print axioms totalDyadicProfileLoss_eq_zero_of_all_strict
#print axioms strict_profile_capacity_of_soft_overlap_le_holes

end OrderedEdgeColoring
end JSP000404Research
