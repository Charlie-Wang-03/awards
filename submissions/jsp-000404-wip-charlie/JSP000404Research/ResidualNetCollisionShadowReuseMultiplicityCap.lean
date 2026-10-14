import JSP000404Research.ResidualNetCollisionGlobalSoftShadowReuse
import Mathlib.Data.Finset.Powerset
import Mathlib.Tactic

/-!
# GLOBAL finite two-bit SOFT shadow reuse multiplicity

A genuine SOFT word can be a Hamming-distance-two shadow of more than
one canonical diagonal target, so it must NOT be counted as an
independently unreserved payment at every target.

For a fixed SOFT word s, the differing two-bit coordinate set uniquely
determines each target d. Therefore there are at most choose(n,2)
targets at Hamming distance exactly two from s.

Together with the exact global SOFT target-incidence double count this
gives a sound, multiplicity-adjusted GLOBAL bound on actual NET
duplicate debt, without asserting nonexistent unique payment.
-/

namespace JSP000404Research
namespace OrderedEdgeColoring

/-- Exact distance-two target capacity per fixed original SOFT word.
Each target is injected into its two-element difference support. -/
theorem hamming_two_targets_card_le_choose
    {n : ℕ}
    (D : Finset (Fin n → Bool))
    (s : Fin n → Bool) :
    (D.filter (fun d =>
      (Finset.univ.filter (fun i : Fin n => s i ≠ d i)).card = 2)).card
      ≤ Nat.choose n 2 := by
  classical
  let S : Finset (Fin n → Bool) :=
    D.filter (fun d =>
      (Finset.univ.filter (fun i : Fin n => s i ≠ d i)).card = 2)
  let f : (Fin n → Bool) → Finset (Fin n) :=
    fun d => Finset.univ.filter (fun i : Fin n => s i ≠ d i)
  have hinj : Set.InjOn f (S : Set (Fin n → Bool)) := by
    intro d hd e he hde
    funext i
    have hi : (s i ≠ d i) ↔ (s i ≠ e i) := by
      have h := congrArg (fun t : Finset (Fin n) => i ∈ t) hde
      simpa [f] using h
    cases hs : s i <;> cases hd' : d i <;>
      cases he' : e i <;> simp_all
  have himage :
      S.image f ⊆ Finset.powersetCard 2 (Finset.univ : Finset (Fin n)) := by
    intro t ht
    obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp ht
    exact Finset.mem_powersetCard.mpr
      ⟨Finset.subset_univ _, (Finset.mem_filter.mp hd).2⟩
  change S.card ≤ Nat.choose n 2
  calc
    S.card = (S.image f).card :=
      (Finset.card_image_of_injOn hinj).symm
    _ ≤ (Finset.powersetCard 2 (Finset.univ : Finset (Fin n))).card :=
      Finset.card_le_card himage
    _ = Nat.choose n 2 := by simp

/-- The global actual NET duplicate debt cannot exceed
choose(n,2) copies of the ACTUAL covered SOFT shadow inventory.
This factor is a rigorously counted cross-target REUSE multiplicity,
NOT a true-hole payment or a free dyadic credit. -/
theorem net_collision_duplicate_debt_le_choose_mul_soft_shadow_mass
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexp : ∀ v, exponent v ≤ n)
    (honeLoss : ∀ v, (active C v).card ≤ n - exponent v + 1) :
    netCollisionCertifiedDuplicateDebt C exponent hexp honeLoss ≤
      (softOverlapCompletionWords C).card * Nat.choose n 2 := by
  classical
  let D := netCollisionCertifiedDiagonalWords C exponent hexp honeLoss
  have h := net_collision_duplicate_debt_le_global_soft_shadow_incidence
    C exponent hexp honeLoss
  change netCollisionCertifiedDuplicateDebt C exponent hexp honeLoss ≤
    ∑ s ∈ softOverlapCompletionWords C,
      (D.filter (fun d =>
        (Finset.univ.filter (fun i : Fin n => s i ≠ d i)).card = 2)).card at h
  calc
    netCollisionCertifiedDuplicateDebt C exponent hexp honeLoss ≤
      ∑ s ∈ softOverlapCompletionWords C,
        (D.filter (fun d =>
          (Finset.univ.filter (fun i : Fin n => s i ≠ d i)).card = 2)).card := h
    _ ≤ ∑ _s ∈ softOverlapCompletionWords C, Nat.choose n 2 := by
      apply Finset.sum_le_sum
      intro s hs
      exact hamming_two_targets_card_le_choose D s
    _ = (softOverlapCompletionWords C).card * Nat.choose n 2 := by simp

#print axioms hamming_two_targets_card_le_choose
#print axioms net_collision_duplicate_debt_le_choose_mul_soft_shadow_mass

end OrderedEdgeColoring
end JSP000404Research
