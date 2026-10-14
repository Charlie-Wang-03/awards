import JSP000404Research.ResidualNetCollisionGlobalSoftShadowReuse
import Mathlib.Tactic

/-!
# A non-reused FIRST-HIT charge in the exact global NET/SOFT ledger

Every truly HIT NET target consumes one distinct first source. Beyond
that, only its surplus preimages contribute to the duplicate debt.
We explicitly account for both with the finite-map fibre identity,
and compare ALL source mass to the actual, possibly REUSED,
Hamming-two SOFT shadow incidence sum.

No SOFT shadow is treated as a true Boolean hole or as independently
unreserved dyadic surplus. This is a corrected covered-incidence
upper bound, not a solution of the six-source global payment.
-/

namespace JSP000404Research
namespace OrderedEdgeColoring

/-- Generic exact finite-image accounting before any geometric
specialization; fibre capacities are counted over distinct images. -/
theorem finite_image_duplicate_plus_first_hits_le_fibre_caps
    {α β : Type*} [DecidableEq α] [DecidableEq β]
    (S : Finset α) (f : α → β) (cap : β → ℕ)
    (hcap : ∀ d ∈ S.image f,
      (S.filter (fun x => f x = d)).card ≤ cap d) :
    S.card - (S.image f).card + (S.image f).card ≤
      ∑ d ∈ S.image f, cap d := by
  classical
  have himage : (S.image f).card ≤ S.card := Finset.card_image_le
  have hfibre :
      S.card = ∑ d ∈ S.image f,
        (S.filter (fun x => f x = d)).card := by
    exact Finset.card_eq_sum_card_fiberwise
      (fun x hx => Finset.mem_image.mpr ⟨x, hx, rfl⟩)
  calc
    S.card - (S.image f).card + (S.image f).card = S.card :=
      Nat.sub_add_cancel himage
    _ = ∑ d ∈ S.image f,
      (S.filter (fun x => f x = d)).card := hfibre
    _ ≤ ∑ d ∈ S.image f, cap d := by
      apply Finset.sum_le_sum
      intro d hd
      exact hcap d hd

/-- Unlike the coarser E_D-only inequality, the right side must
account for every first-hit diagonal AND the exact duplicate excess.
These are ACTUAL covered SOFT target-shadow incidences. -/
theorem net_duplicate_plus_distinct_hits_le_soft_shadow_incidence
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexp : ∀ v, exponent v ≤ n)
    (honeLoss : ∀ v, (active C v).card ≤ n - exponent v + 1) :
    netCollisionCertifiedDuplicateDebt C exponent hexp honeLoss +
      (netCollisionCertifiedDiagonalWords C exponent hexp honeLoss).card ≤
      ∑ s ∈ softOverlapCompletionWords C,
        ((netCollisionCertifiedDiagonalWords C exponent hexp honeLoss).filter
          (fun d =>
            (Finset.univ.filter (fun i : Fin n => s i ≠ d i)).card = 2)).card := by
  classical
  let S := {w : Fin n → Bool //
    w ∈ netActualForwardReverseCollisionWords C exponent hexp honeLoss}
  let f : S → Fin n → Bool :=
    netCollisionCertifiedDiagonal C exponent hexp honeLoss
  let D := netCollisionCertifiedDiagonalWords C exponent hexp honeLoss
  have htarget :
      (Finset.univ : Finset S).card -
          ((Finset.univ : Finset S).image f).card +
          ((Finset.univ : Finset S).image f).card ≤
        ∑ d ∈ (Finset.univ : Finset S).image f,
          (targetHammingTwoSoftOverlapWords C d).card := by
    apply finite_image_duplicate_plus_first_hits_le_fibre_caps
      (Finset.univ : Finset S) f
      (fun d => (targetHammingTwoSoftOverlapWords C d).card)
    intro d hd
    exact net_collision_target_fibre_card_le_local_soft_sphere
      C exponent hexp honeLoss d
  have haccount :
      netCollisionCertifiedDuplicateDebt C exponent hexp honeLoss + D.card ≤
        ∑ d ∈ D, (targetHammingTwoSoftOverlapWords C d).card := by
    simpa only [D, S, f, netCollisionCertifiedDuplicateDebt,
      netCollisionCertifiedDiagonalWords, netCollisionCertifiedDiagonalFibre,
      Finset.card_univ, Fintype.card_coe] using htarget
  have hdouble := soft_hamming_two_shadow_incidence_double_count C D
  calc
    netCollisionCertifiedDuplicateDebt C exponent hexp honeLoss + D.card ≤
      ∑ d ∈ D, (targetHammingTwoSoftOverlapWords C d).card := haccount
    _ = ∑ s ∈ softOverlapCompletionWords C,
        (D.filter (fun d =>
          (Finset.univ.filter (fun i : Fin n => s i ≠ d i)).card = 2)).card :=
        hdouble

#print axioms finite_image_duplicate_plus_first_hits_le_fibre_caps
#print axioms net_duplicate_plus_distinct_hits_le_soft_shadow_incidence

end OrderedEdgeColoring
end JSP000404Research
