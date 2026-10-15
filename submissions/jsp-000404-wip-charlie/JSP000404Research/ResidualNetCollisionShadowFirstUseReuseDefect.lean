import JSP000404Research.ResidualNetCollisionShadowFirstHitGlobalCharge
import Mathlib.Tactic

/-!
# Actual NET/SOFT global first-use and cross-target reuse defect

The global incidence ledger is refined into TWO DISJOINT numerical parts:
- one FIRST-USE unit for each ACTUAL SOFT word adjacent to at least
  one ACTUALLY HIT NET diagonal;
- one EXTRA unit for every additional target served by the same
  SOFT shadow word.

This measures the exact obstruction to a "charge each SOFT word
once" argument, without falsely assuming global source disjointness
or granting covered SOFT words status as true Boolean holes.

If a future geometric lemma proves each such SOFT word is adjacent to
at most one actual target, the reuse defect vanishes and the first-hit
ledger injects into the cardinality of actual SOFT words.
-/

namespace JSP000404Research
namespace OrderedEdgeColoring

/-- Any finite degree ledger is exactly "first uses + additional uses".
For zero degree, both contributions vanish; for positive degree,
one contribution is the first use and the rest are recycled uses. -/
theorem finite_degree_first_use_plus_reuse_exact
    {α : Type*} [DecidableEq α]
    (S : Finset α) (deg : α → ℕ) :
    (∑ s ∈ S, deg s) =
      (S.filter (fun s => 0 < deg s)).card +
        ∑ s ∈ S, (deg s - 1) := by
  classical
  have hused :
      (S.filter (fun s => 0 < deg s)).card =
        ∑ s ∈ S, if 0 < deg s then 1 else 0 := by
    simpa using (Finset.card_filter (fun s => 0 < deg s) S)
  calc
    (∑ s ∈ S, deg s) =
        ∑ s ∈ S, ((if 0 < deg s then 1 else 0) + (deg s - 1)) := by
      apply Finset.sum_congr rfl
      intro s hs
      split_ifs <;> omega
    _ = (∑ s ∈ S, if 0 < deg s then 1 else 0) +
          (∑ s ∈ S, (deg s - 1)) := Finset.sum_add_distrib
    _ = (S.filter (fun s => 0 < deg s)).card +
          ∑ s ∈ S, (deg s - 1) := by rw [hused]

/-- Exact ACTUAL SOFT shadow incidence decomposition across the
distinct NET image D: only first-shadow uses count as fresh words. -/
theorem net_actual_soft_shadow_incidence_eq_first_uses_plus_reuse
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexp : ∀ v, exponent v ≤ n)
    (honeLoss : ∀ v, (active C v).card ≤ n - exponent v + 1) :
    let D := netCollisionCertifiedDiagonalWords C exponent hexp honeLoss
    let S := softOverlapCompletionWords C
    let deg : (Fin n → Bool) → ℕ := fun s =>
      (D.filter (fun d =>
        (Finset.univ.filter (fun i : Fin n => s i ≠ d i)).card = 2)).card
    (∑ s ∈ S, deg s) =
      (S.filter (fun s => 0 < deg s)).card +
        ∑ s ∈ S, (deg s - 1) := by
  classical
  -- Avoid eager zeta-reduction of the large certified NET definition:
  -- its expansion during `dsimp only` exhausts the heartbeat budget.
  -- `exact` can instantiate the generic finite-degree lemma directly.
  exact finite_degree_first_use_plus_reuse_exact
    (softOverlapCompletionWords C)
    (fun s => ((netCollisionCertifiedDiagonalWords C exponent hexp honeLoss).filter
      (fun d =>
        (Finset.univ.filter (fun i : Fin n => s i ≠ d i)).card = 2)).card)

/-- Necessary GLOBAL source debt inequality with the true cross-target
reuse defect retained, rather than silently spending one SOFT word
once for all the targets it shadows. -/
theorem net_duplicate_first_hits_le_used_soft_plus_reuse_defect
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexp : ∀ v, exponent v ≤ n)
    (honeLoss : ∀ v, (active C v).card ≤ n - exponent v + 1) :
    let D := netCollisionCertifiedDiagonalWords C exponent hexp honeLoss
    let S := softOverlapCompletionWords C
    let deg : (Fin n → Bool) → ℕ := fun s =>
      (D.filter (fun d =>
        (Finset.univ.filter (fun i : Fin n => s i ≠ d i)).card = 2)).card
    netCollisionCertifiedDuplicateDebt C exponent hexp honeLoss + D.card ≤
      (S.filter (fun s => 0 < deg s)).card +
        ∑ s ∈ S, (deg s - 1) := by
  classical
  dsimp only
  let D := netCollisionCertifiedDiagonalWords C exponent hexp honeLoss
  let S := softOverlapCompletionWords C
  let deg : (Fin n → Bool) → ℕ := fun s =>
      (D.filter (fun d =>
        (Finset.univ.filter (fun i : Fin n => s i ≠ d i)).card = 2)).card
  have hledger :=
    net_duplicate_plus_distinct_hits_le_soft_shadow_incidence
      C exponent hexp honeLoss
  have hsplit := finite_degree_first_use_plus_reuse_exact S deg
  change netCollisionCertifiedDuplicateDebt C exponent hexp honeLoss +
      D.card ≤ (∑ s ∈ S, deg s) at hledger
  exact hledger.trans_eq hsplit

/-- Exact missing condition for a unique-shadow count to be valid:
if each ACTUAL SOFT word shadows at most ONE actually hit diagonal,
then duplicate debt PLUS first hits fits into |SOFT words|. No
claim is made that the condition always holds geometrically. -/
theorem net_duplicate_first_hits_le_soft_words_of_no_cross_target_reuse
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexp : ∀ v, exponent v ≤ n)
    (honeLoss : ∀ v, (active C v).card ≤ n - exponent v + 1)
    (hnoreuse :
      ∀ s ∈ softOverlapCompletionWords C,
        ((netCollisionCertifiedDiagonalWords C exponent hexp honeLoss).filter
          (fun d =>
            (Finset.univ.filter (fun i : Fin n => s i ≠ d i)).card = 2)).card ≤ 1) :
    netCollisionCertifiedDuplicateDebt C exponent hexp honeLoss +
      (netCollisionCertifiedDiagonalWords C exponent hexp honeLoss).card ≤
        (softOverlapCompletionWords C).card := by
  classical
  let D := netCollisionCertifiedDiagonalWords C exponent hexp honeLoss
  let S := softOverlapCompletionWords C
  let deg : (Fin n → Bool) → ℕ := fun s =>
    (D.filter (fun d =>
      (Finset.univ.filter (fun i : Fin n => s i ≠ d i)).card = 2)).card
  have hreuse : (∑ s ∈ S, (deg s - 1)) = 0 := by
    apply Finset.sum_eq_zero
    intro s hs
    have h := hnoreuse s hs
    change deg s ≤ 1 at h
    omega
  have hbudget := net_duplicate_first_hits_le_used_soft_plus_reuse_defect
    C exponent hexp honeLoss
  change netCollisionCertifiedDuplicateDebt C exponent hexp honeLoss +
    D.card ≤ (S.filter (fun s => 0 < deg s)).card +
      (∑ s ∈ S, (deg s - 1)) at hbudget
  rw [hreuse, add_zero] at hbudget
  exact hbudget.trans
    (Finset.card_le_card (Finset.filter_subset _ _))

/-- An actually attained NET image consisting of at most one
diagonal has no cross-target SOFT shadow reuse. This is a genuine
conditional closure, not a claim that planar AngleCap forces a
singleton target image or supplies any other missing payments. -/
theorem net_duplicate_first_hits_le_soft_words_of_singleton_target_image
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexp : ∀ v, exponent v ≤ n)
    (honeLoss : ∀ v, (active C v).card ≤ n - exponent v + 1)
    (honeTarget :
      (netCollisionCertifiedDiagonalWords C exponent hexp honeLoss).card ≤ 1) :
    netCollisionCertifiedDuplicateDebt C exponent hexp honeLoss +
      (netCollisionCertifiedDiagonalWords C exponent hexp honeLoss).card ≤
        (softOverlapCompletionWords C).card := by
  classical
  apply net_duplicate_first_hits_le_soft_words_of_no_cross_target_reuse
    C exponent hexp honeLoss
  intro s hs
  exact (Finset.card_le_card (Finset.filter_subset _ _)).trans honeTarget

#print axioms finite_degree_first_use_plus_reuse_exact
#print axioms net_actual_soft_shadow_incidence_eq_first_uses_plus_reuse
#print axioms net_duplicate_first_hits_le_used_soft_plus_reuse_defect
#print axioms net_duplicate_first_hits_le_soft_words_of_no_cross_target_reuse
#print axioms net_duplicate_first_hits_le_soft_words_of_singleton_target_image

end OrderedEdgeColoring
end JSP000404Research
