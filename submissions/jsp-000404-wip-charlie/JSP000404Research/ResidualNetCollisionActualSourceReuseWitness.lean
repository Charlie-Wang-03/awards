import JSP000404Research.ResidualNetCollisionActualReuseWitness
import Mathlib.Tactic

/-!
# Failure of NET SOFT first-hit payment yields two original collision sinks

The previous actual-shadow witness constructed s,d,e with d,e belonging
to the ACTUAL certified diagonal image. Here we peel back that image
definition to exhibit two genuinely attained NET forward/reverse collision
words w₁,w₂. Each such word already has unique original forward-hard and
reverse-strict-rigid sources through the certified witness lemmas.

This bridges the local reuse obstruction from abstract image points
back to genuine source words without assuming a new planar separation,
TRUE hole, or unreserved surplus payment.
-/

namespace JSP000404Research
namespace OrderedEdgeColoring

/-- Under a strict shortage of distinct actual SOFT shadows, there is
an actual SOFT word shared by the certified diagonals of TWO ACTUAL NET
collision sink words, with those two diagonal targets differing on
exactly two or four coordinates. No synthetic NET targets are used. -/
theorem net_first_hit_shortage_forces_two_actual_collision_sources
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
        netCollisionCertifiedDiagonal C exponent hexp honeLoss w₁ ≠
          netCollisionCertifiedDiagonal C exponent hexp honeLoss w₂ ∧
        (Finset.univ.filter (fun i : Fin n =>
          s i ≠ (netCollisionCertifiedDiagonal C exponent hexp honeLoss w₁) i)).card = 2 ∧
        (Finset.univ.filter (fun i : Fin n =>
          s i ≠ (netCollisionCertifiedDiagonal C exponent hexp honeLoss w₂) i)).card = 2 ∧
        ((Finset.univ.filter (fun i : Fin n =>
          (netCollisionCertifiedDiagonal C exponent hexp honeLoss w₁) i ≠
          (netCollisionCertifiedDiagonal C exponent hexp honeLoss w₂) i)).card = 2 ∨
         (Finset.univ.filter (fun i : Fin n =>
          (netCollisionCertifiedDiagonal C exponent hexp honeLoss w₁) i ≠
          (netCollisionCertifiedDiagonal C exponent hexp honeLoss w₂) i)).card = 4) := by
  classical
  obtain ⟨s, hs, d, hd, e, he, hde, hsd, hse, hdist⟩ :=
    net_first_hit_shortage_forces_actual_shared_soft_witness
      C exponent hexp honeLoss hfail
  unfold netCollisionCertifiedDiagonalWords at hd he
  obtain ⟨w₁, _, hw₁⟩ := Finset.mem_image.mp hd
  obtain ⟨w₂, _, hw₂⟩ := Finset.mem_image.mp he
  refine ⟨s, hs, w₁, w₂, ?_, ?_, ?_, ?_⟩
  · intro h
    exact hde (hw₁.symm.trans (h.trans hw₂))
  · simpa only [hw₁] using hsd
  · simpa only [hw₂] using hse
  · rcases hdist with htwo | hfour
    · left
      simpa only [hw₁, hw₂] using htwo
    · right
      simpa only [hw₁, hw₂] using hfour

#print axioms net_first_hit_shortage_forces_two_actual_collision_sources

end OrderedEdgeColoring
end JSP000404Research
