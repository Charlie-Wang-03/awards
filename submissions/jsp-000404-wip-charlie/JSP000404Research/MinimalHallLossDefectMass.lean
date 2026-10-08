import JSP000404Research.ResidualEnlargedCandidateHall
import Mathlib.Tactic

/-!
# Quantitative Hall deficit forces shared loss-cube mass

For an inclusion-minimal deficient enlarged candidate family T, its
actual positive weighted deficit is

  Delta(T) = sum_{v in T} 2^exponent(v) -
             card(union_{v in T} B(v)).

If v is a projected-loss centre with exponent(v)<n, the established
all-active enlarged block has one whole retained completion cube of
local slack in addition to its target 2^exponent(v).

The deletion inequality for a minimal deficient set charges both the
full local slack and the ENTIRE actual Hall deficit to the words of
B(v) shared with other vertices:

  card(shared(v,T)) >= card(Q_v) + Delta(T).

This is sharper than card(Q_v)+1 whenever the deficit exceeds one.
It neither presupposes geometric exclusion of all collisions nor
asserts the missing global Hall expansion.
-/

namespace JSP000404Research
namespace OrderedEdgeColoring

theorem minimal_loss_shared_card_ge_cube_add_deficit
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    {T : Finset V}
    (hdef :
      BlockDeficient
        (fun i => 2 ^ exponent i)
        (enlargedProjectedCandidateBlock C exponent) T)
    (hmin :
      ∀ U : Finset V, U ⊂ T →
        ¬ BlockDeficient
          (fun i => 2 ^ exponent i)
          (enlargedProjectedCandidateBlock C exponent) U)
    {v : V}
    (hvT : v ∈ T)
    (hvLoss : v ∈ projectedLossVertices C exponent)
    (hvLt : exponent v < n) :
    (retainedCompletionWords C v).card +
        blockDeficiencyAmount
          (fun i => 2 ^ exponent i)
          (enlargedProjectedCandidateBlock C exponent) T
      ≤
    (sharedBlockWords
      (enlargedProjectedCandidateBlock C exponent) T v).card := by
  classical
  let B := enlargedProjectedCandidateBlock C exponent
  let demand : V → ℕ := fun i => 2 ^ exponent i
  have hslack :
      demand v + (retainedCompletionWords C v).card ≤
        (B v).card :=
    enlargedProjectedCandidateBlock_loss_slack
      C exponent hvLoss hvLt
  have hlocal : demand v ≤ (B v).card := by
    omega
  have hcharged :
      blockDeficiencyAmount demand B T +
          ((B v).card - demand v)
        ≤ (sharedBlockWords B T v).card :=
    minimal_deficient_amount_le_shared_excess
      demand B hdef hmin hvT hlocal
  change (retainedCompletionWords C v).card +
      blockDeficiencyAmount demand B T ≤
    (sharedBlockWords B T v).card
  omega

/-- In a true minimal deficiency, the shared mass at each sub-top
loss centre exceeds one full completion cube by a positive amount. -/
theorem minimal_loss_shared_strictly_exceeds_cube
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    {T : Finset V}
    (hdef :
      BlockDeficient
        (fun i => 2 ^ exponent i)
        (enlargedProjectedCandidateBlock C exponent) T)
    (hmin :
      ∀ U : Finset V, U ⊂ T →
        ¬ BlockDeficient
          (fun i => 2 ^ exponent i)
          (enlargedProjectedCandidateBlock C exponent) U)
    {v : V}
    (hvT : v ∈ T)
    (hvLoss : v ∈ projectedLossVertices C exponent)
    (hvLt : exponent v < n) :
    (retainedCompletionWords C v).card <
      (sharedBlockWords
        (enlargedProjectedCandidateBlock C exponent) T v).card := by
  have hmass :=
    minimal_loss_shared_card_ge_cube_add_deficit
      C exponent hdef hmin hvT hvLoss hvLt
  have hpos :=
    blockDeficiencyAmount_pos_of_deficient
      (fun i : V => 2 ^ exponent i)
      (enlargedProjectedCandidateBlock C exponent) hdef
  omega

#print axioms minimal_loss_shared_card_ge_cube_add_deficit
#print axioms minimal_loss_shared_strictly_exceeds_cube

end OrderedEdgeColoring
end JSP000404Research
