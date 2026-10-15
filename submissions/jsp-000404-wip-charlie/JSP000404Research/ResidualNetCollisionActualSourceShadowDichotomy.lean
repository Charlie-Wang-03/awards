import JSP000404Research.ResidualNetCollisionActualSourceReuseWitness
import JSP000404Research.ResidualTwoShadowTwoBitOverlap
import JSP000404Research.ResidualTwoShadowFourBitDisjoint
import Mathlib.Tactic

/-!
# Exact actual NET source / SOFT-shadow reuse support dichotomy

If the certified first-hit NET debt exceeds the number of actual
distinct SOFT overlap words, two ACTUAL NET collision sources w1,w2
and one ACTUAL SOFT word s witness the failure. Their distinct
certified diagonal targets each differ from s in two coordinates.

This module upgrades the witness to an exhaustive support
classification: their target difference is either two bits, with
exactly one shared flip coordinate, or four bits, with disjoint
flip supports. Every target is certified from a genuine source;
nothing here counts a covered SOFT word as a TRUE Boolean hole.

The outstanding six-source geometric payment/surplus allocation
remains unproved.
-/

namespace JSP000404Research
namespace OrderedEdgeColoring

theorem net_first_hit_shortage_actual_source_flip_support_dichotomy
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexp : ∀ v, exponent v ≤ n)
    (honeLoss : ∀ v, (active C v).card ≤ n - exponent v + 1)
    (hfail :
      (softOverlapCompletionWords C).card <
        netCollisionCertifiedDuplicateDebt C exponent hexp honeLoss +
          (netCollisionCertifiedDiagonalWords C exponent hexp honeLoss).card) :
    ∃ s ∈ softOverlapCompletionWords C,
      ∃ w₁ w₂ :
        {w : Fin n → Bool //
          w ∈ netActualForwardReverseCollisionWords
            C exponent hexp honeLoss},
        let d := netCollisionCertifiedDiagonal C exponent hexp honeLoss w₁
        let e := netCollisionCertifiedDiagonal C exponent hexp honeLoss w₂
        let A := Finset.univ.filter (fun i : Fin n => s i ≠ d i)
        let B := Finset.univ.filter (fun i : Fin n => s i ≠ e i)
        let T := Finset.univ.filter (fun i : Fin n => d i ≠ e i)
        d ≠ e ∧ A.card = 2 ∧ B.card = 2 ∧
          ((T.card = 2 ∧ (A ∩ B).card = 1) ∨
           (T.card = 4 ∧ Disjoint A B)) := by
  classical
  obtain ⟨s, hs, w₁, w₂, hne, hsd, hse, hdist⟩ :=
    net_first_hit_shortage_forces_two_actual_collision_sources
      C exponent hexp honeLoss hfail
  refine ⟨s, hs, w₁, w₂, hne, hsd, hse, ?_⟩
  rcases hdist with htwo | hfour
  · left
    exact ⟨htwo,
      shared_two_shadow_two_bit_flip_intersection_card_one
        s
        (netCollisionCertifiedDiagonal C exponent hexp honeLoss w₁)
        (netCollisionCertifiedDiagonal C exponent hexp honeLoss w₂)
        hsd hse htwo⟩
  · right
    exact ⟨hfour,
      shared_two_shadow_four_bit_flips_disjoint
        s
        (netCollisionCertifiedDiagonal C exponent hexp honeLoss w₁)
        (netCollisionCertifiedDiagonal C exponent hexp honeLoss w₂)
        hsd hse hfour⟩

#print axioms net_first_hit_shortage_actual_source_flip_support_dichotomy

end OrderedEdgeColoring
end JSP000404Research
