import JSP000404Research.ResidualNetCollisionSupportFibreMultiplicity
import Mathlib.Tactic

/-!
# Exact fibrewise accounting of ACTUAL canonical duplicate-image debt

The certified diagonal-image DUPLICATION debt was defined as
  |genuine NET source collisions| - |distinct canonical diagonals|.

Here we show it equals the sum, over DISTINCT actual diagonal targets d,
of the number of EXTRA source collisions landing on d beyond its first
source. Every summand is a specific genuine target fibre, and each
fibre is nonempty and has an injective unordered-original-colour tag.

This is an EXACT local-to-global account, not a new hole payment.
The remaining 2/4-bit cross-support witnesses are still possible.
-/

namespace JSP000404Research
namespace OrderedEdgeColoring

/-- Generic finite-map identity: the global loss from merging equal
images is EXACTLY the sum of the excess preimages of each distinct
image point. No injectivity is assumed. -/
theorem finset_image_duplicate_debt_eq_sum_fibre_excess
    {α β : Type*} [DecidableEq α] [DecidableEq β]
    (S : Finset α) (f : α → β) :
    S.card - (S.image f).card =
      ∑ d ∈ S.image f,
        ((S.filter (fun s => f s = d)).card - 1) := by
  classical
  have hpositive :
      ∀ d ∈ S.image f,
        1 ≤ (S.filter (fun s => f s = d)).card := by
    intro d hd
    obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp hd
    have hm : s ∈ S.filter (fun x => f x = f s) :=
      Finset.mem_filter.mpr ⟨hs, rfl⟩
    exact Finset.one_le_card.mpr ⟨s, hm⟩
  have hsum :
      S.card = ∑ d ∈ S.image f,
        (S.filter (fun s => f s = d)).card := by
    exact Finset.card_eq_sum_card_fiberwise (fun s hs =>
      Finset.mem_image.mpr ⟨s, hs, rfl⟩)
  have hexact :
      (∑ d ∈ S.image f,
        ((S.filter (fun s => f s = d)).card - 1)) +
      (S.image f).card = S.card := by
    calc
      (∑ d ∈ S.image f,
        ((S.filter (fun s => f s = d)).card - 1)) +
        (S.image f).card =
        ∑ d ∈ S.image f,
          (((S.filter (fun s => f s = d)).card - 1) + 1) := by
            rw [Finset.sum_add_distrib]
            simp
      _ = ∑ d ∈ S.image f,
          (S.filter (fun s => f s = d)).card := by
            apply Finset.sum_congr rfl
            intro d hd
            have hp := hpositive d hd
            omega
      _ = S.card := hsum.symm
  omega

/-- Actual canonical source fibre over a concrete Boolean diagonal
target; the colour-pair owner of each member is uniquely known. -/
noncomputable def netCollisionCertifiedDiagonalFibre
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexp : ∀ v, exponent v ≤ n)
    (honeLoss : ∀ v, (active C v).card ≤ n - exponent v + 1)
    (d : Fin n → Bool) :
    Finset {w : Fin n → Bool //
      w ∈ netActualForwardReverseCollisionWords
        C exponent hexp honeLoss} :=
  Finset.univ.filter
    (fun s => netCollisionCertifiedDiagonal C exponent hexp honeLoss s = d)

/-- The global ACTUAL canonical duplicate-image debt is precisely
the TOTAL excess source-fibre cardinal, one extra charge for
each source beyond the first over the SAME target d.
No global hole reuse or source-fibre injectivity is smuggled in. -/
theorem net_collision_certified_duplicate_debt_eq_sum_fibre_excess
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexp : ∀ v, exponent v ≤ n)
    (honeLoss : ∀ v, (active C v).card ≤ n - exponent v + 1) :
    netCollisionCertifiedDuplicateDebt C exponent hexp honeLoss =
      ∑ d ∈ netCollisionCertifiedDiagonalWords C exponent hexp honeLoss,
        (netCollisionCertifiedDiagonalFibre
          C exponent hexp honeLoss d).card - 1 := by
  classical
  let S := {w : Fin n → Bool //
      w ∈ netActualForwardReverseCollisionWords
        C exponent hexp honeLoss}
  let f : S → Fin n → Bool :=
    netCollisionCertifiedDiagonal C exponent hexp honeLoss
  have h := finset_image_duplicate_debt_eq_sum_fibre_excess
    (Finset.univ : Finset S) f
  change (netActualForwardReverseCollisionWords C exponent hexp honeLoss).card -
      (Finset.univ.image f).card =
    ∑ d ∈ Finset.univ.image f,
      ((Finset.univ.filter (fun s : S => f s = d)).card - 1) at h
  simpa only [netCollisionCertifiedDuplicateDebt,
    netCollisionCertifiedDiagonalWords,
    netCollisionCertifiedDiagonalFibre,
    Finset.card_univ, Fintype.card_coe] using h

#print axioms finset_image_duplicate_debt_eq_sum_fibre_excess
#print axioms net_collision_certified_duplicate_debt_eq_sum_fibre_excess

end OrderedEdgeColoring
end JSP000404Research
