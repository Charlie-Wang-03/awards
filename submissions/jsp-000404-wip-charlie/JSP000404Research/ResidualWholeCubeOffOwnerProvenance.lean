import JSP000404Research.ResidualWholeCubeOffOwnerExit
import JSP000404Research.ResidualLossRecursiveOutlet
import Mathlib.Tactic

/-!
# Provenance-preserving whole-cube off-owner recursive outlet

The legacy off-owner recursive outlet kept the displaced coordinate but dropped
the crucial fact that the recursive word itself lies in the translated slice
of the source. That fact is already supplied by the minimal-core augmenting
witness.

This module preserves it in the exact/loss-fibre branch. No new hypothesis is
introduced.
-/

namespace JSP000404Research
namespace OrderedEdgeColoring

def TranslatedExactLossFibre
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (source : V) (d : Fin n) : Prop :=
  ∃ y : Fin n → Bool,
    y ∈ translatedCompletionWords C source d ∧
    (completionFibre C y).Nonempty ∧
    (completionFibre C y).card ≤ 2 ∧
    (∀ w : V,
      w ∈ completionFibre C y →
      w ≠ source ∧
      (
        ExactProjectedBudget C exponent w
        ∨
        w ∈ projectedLossVertices C exponent
      ))

theorem wholeCube_offOwner_exit_hole_or_paid_or_translated_exact_loss_fibre
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexp : ∀ q, exponent q ≤ n)
    (honeLoss :
      ∀ q, (active C q).card ≤ n - exponent q + 1)
    (hn3 : 3 ≤ n)
    {T : Finset V}
    (hdef :
      BlockDeficient
        (fun q => 2 ^ exponent q)
        (enlargedProjectedCandidateBlock C exponent)
        T)
    (hmin :
      ∀ U : Finset V,
        U ⊂ T →
        ¬ BlockDeficient
          (fun q => 2 ^ exponent q)
          (enlargedProjectedCandidateBlock C exponent)
          U)
    {s v : V} {c : Fin n}
    (hvT : v ∈ T)
    (hsv : s ≠ v)
    (hsLoss : s ∈ projectedLossVertices C exponent)
    (hvLoss : v ∈ projectedLossVertices C exponent)
    (hvSecond : exponent v = n - 2)
    (hcV : c ∈ retainedActive C v)
    (hwhole : WholeCubeQTPair C s v c) :
    ∃ d : Fin n,
      d ∈ retainedActive C v ∧
      d ≠ c ∧
      (
        ∃ y : Fin n → Bool,
          y ∉ coveredCompletionWords C
      )
      ∨
      (
        ∃ y : Fin n → Bool,
        ∃ w : V,
          y ∈ retainedCompletionWords C w ∧
          1 ≤ dyadicProfileSurplus
            exponent (projectedFree C) w
      )
      ∨
      TranslatedExactLossFibre C exponent v d := by
  obtain ⟨y,d,w,hdActive,hdc,hyT,_hwBlock,
      _hnotV,_hnotS,_hwT,_hwNeV,_hwNeS⟩ :=
    minimal_core_wholeCubeQTPair_has_off_owner_third_exit
      C exponent hn3 hdef hmin
      hvT hsv hsLoss hvLoss hvSecond hcV hwhole

  let x : Fin n → Bool := flipBoolWordAt y d
  have hxQ :
      x ∈ retainedCompletionWords C v := by
    exact (mem_translatedCompletionWords C v d y).1 hyT
  have hyEq :
      flipBoolWordAt x d = y := by
    dsimp [x]
    exact flipBoolWordAt_involutive d y

  rcases
    projectedLoss_word_hole_or_strict_paid_or_exact_loss_fibre
      C exponent hexp honeLoss hvLoss hxQ hdActive
    with hhole | hpaid | hfibre

  · refine ⟨d,hdActive,hdc,Or.inl ?_⟩
    refine ⟨y,?_⟩
    simpa [x,hyEq] using hhole

  · refine ⟨d,hdActive,hdc,Or.inr (Or.inl ?_)⟩
    obtain ⟨w',hw'Q,hw'Paid⟩ := hpaid
    refine ⟨y,w',?_,hw'Paid⟩
    simpa [x,hyEq] using hw'Q

  · refine ⟨d,hdActive,hdc,Or.inr (Or.inr ?_)⟩
    refine ⟨y,hyT,?_,?_,?_⟩
    · simpa [x,hyEq] using hfibre.1
    · simpa [x,hyEq] using hfibre.2.1
    · intro w' hw'
      have hw'' :
          w' ∈ completionFibre C (flipBoolWordAt x d) := by
        simpa [hyEq] using hw'
      exact hfibre.2.2 w' hw''

#print axioms wholeCube_offOwner_exit_hole_or_paid_or_translated_exact_loss_fibre

end OrderedEdgeColoring
end JSP000404Research
