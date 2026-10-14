import JSP000404Research.ResidualNetCollisionLocalSoftSphereCapacity
import Mathlib.Tactic

/-!
# GLOBAL actual SOFT-shadow reuse ledger (no fictitious unique payment)

For ANY finite set D of Boolean diagonals, count every (d,s)
incidence with d in D, s an ACTUAL SOFT overlap completion word,
and Hamming(d,s) = 2. Double-count the SAME incidence first by target,
then by genuinely covered SOFT word. This is an EXACT equality; no
cross-target disjointness is assumed. A SOFT word reused by multiple
diagonals is explicitly counted that many times.

The actual NET duplicate-image debt is bounded by this precise
cross-target SOFT shadow incidence ledger. This is a COVERED resource
multiplicity account, not a matching of targets to unreserved credits.
-/

namespace JSP000404Research
namespace OrderedEdgeColoring

/-- Exact cross-target SOFT shadow incidence double count. -/
theorem soft_hamming_two_shadow_incidence_double_count
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (D : Finset (Fin n → Bool)) :
    (∑ d ∈ D, (targetHammingTwoSoftOverlapWords C d).card) =
      ∑ s ∈ softOverlapCompletionWords C,
        (D.filter (fun d =>
          (Finset.univ.filter (fun i : Fin n => s i ≠ d i)).card = 2)).card := by
  classical
  let H : (Fin n → Bool) → (Fin n → Bool) → Prop :=
    fun s d => (Finset.univ.filter (fun i : Fin n => s i ≠ d i)).card = 2
  have htarget (d : Fin n → Bool) :
      (targetHammingTwoSoftOverlapWords C d).card =
        ∑ s ∈ softOverlapCompletionWords C, if H s d then 1 else 0 := by
    simpa only [targetHammingTwoSoftOverlapWords, H] using
      (Finset.card_filter (fun s => H s d) (softOverlapCompletionWords C))
  have hsoft (s : Fin n → Bool) :
      (D.filter (fun d => H s d)).card =
        ∑ d ∈ D, if H s d then 1 else 0 := by
    simpa using (Finset.card_filter (fun d => H s d) D)
  calc
    (∑ d ∈ D, (targetHammingTwoSoftOverlapWords C d).card) =
      ∑ d ∈ D, ∑ s ∈ softOverlapCompletionWords C,
        if H s d then 1 else 0 := by
        apply Finset.sum_congr rfl
        intro d hd
        exact htarget d
    _ = ∑ s ∈ softOverlapCompletionWords C, ∑ d ∈ D,
          if H s d then 1 else 0 := by
          rw [Finset.sum_comm]
    _ = ∑ s ∈ softOverlapCompletionWords C,
        (D.filter (fun d => H s d)).card := by
          apply Finset.sum_congr rfl
          intro s hs
          exact (hsoft s).symm
    _ = ∑ s ∈ softOverlapCompletionWords C,
        (D.filter (fun d =>
          (Finset.univ.filter (fun i : Fin n => s i ≠ d i)).card = 2)).card := rfl

/-- Certified NET duplicate debt is controlled by the TRUE global
SOFT shadow incidence count. Each SOFT word is charged according
to its number of nearby ACTUALLY HIT diagonals, never just once. -/
theorem net_collision_duplicate_debt_le_global_soft_shadow_incidence
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexp : ∀ v, exponent v ≤ n)
    (honeLoss : ∀ v, (active C v).card ≤ n - exponent v + 1) :
    netCollisionCertifiedDuplicateDebt C exponent hexp honeLoss ≤
      ∑ s ∈ softOverlapCompletionWords C,
        ((netCollisionCertifiedDiagonalWords C exponent hexp honeLoss).filter
          (fun d =>
            (Finset.univ.filter (fun i : Fin n => s i ≠ d i)).card = 2)).card := by
  classical
  let D := netCollisionCertifiedDiagonalWords C exponent hexp honeLoss
  have hlocal :=
    net_collision_duplicate_debt_le_local_soft_sphere_excess
      C exponent hexp honeLoss
  have hdrop :
      (∑ d ∈ D, (targetHammingTwoSoftOverlapWords C d).card - 1) ≤
        ∑ d ∈ D, (targetHammingTwoSoftOverlapWords C d).card := by
    apply Finset.sum_le_sum
    intro d hd
    omega
  have hdouble := soft_hamming_two_shadow_incidence_double_count C D
  exact (hlocal.trans hdrop).trans hdouble

#print axioms soft_hamming_two_shadow_incidence_double_count
#print axioms net_collision_duplicate_debt_le_global_soft_shadow_incidence

end OrderedEdgeColoring
end JSP000404Research
