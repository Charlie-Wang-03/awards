import JSP000404Research.ResidualWholeCubeOffOwnerExit
import JSP000404Research.ResidualAugmentingState
import JSP000404Research.ProjectionLossAugmentingTransition
import Mathlib.Tactic

/-!
# Structural transition from a whole-cube off-owner exit

The minimal-core whole-cube argument produces

  y ∈ T_v(d)

with d active at the projected-loss source v and d != c, where c is the
whole-cube coordinate.

Write x = flip_d(y).  Then x ∈ Q_v and y = flip_d(x).  Since every projected
loss completion word is singly covered by its owner, the generic single-flip
structural transition applies.

Thus the off-owner augmenting exit lands immediately in the standard
multiplicity-0/1/2 state machine while retaining the displaced-coordinate
provenance d != c.
-/

namespace JSP000404Research
namespace OrderedEdgeColoring

theorem wholeCube_offOwner_structural_transition
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
        (∃ y : Fin n → Bool,
          y ∉ coveredCompletionWords C)
        ∨
        (∃ y : Fin n → Bool,
         ∃ w : V,
          IsSingleCompletionWord C w y ∧
          w ≠ v ∧
          d ∈ retainedActive C w ∧
          retainedBit C w d = !(retainedBit C v d))
        ∨
        (∃ y : Fin n → Bool,
         ∃ u w : V,
          u < w ∧
          IsResidual C u w ∧
          y ∈ retainedCompletionWords C u ∧
          y ∈ retainedCompletionWords C w ∧
          u ≠ v ∧
          w ≠ v ∧
          d ∈ retainedActive C u ∧
          d ∈ retainedActive C w ∧
          retainedBit C u d = !(retainedBit C v d) ∧
          retainedBit C w d = !(retainedBit C v d))
      ) := by
  obtain ⟨y,d,_third,hdActive,hdc,hyT,_hthirdBlock,
      _hnotV,_hnotS,_hthirdT,_hthirdNeV,_hthirdNeS⟩ :=
    minimal_core_wholeCubeQTPair_has_off_owner_third_exit
      C exponent hn3 hdef hmin
      hvT hsv hsLoss hvLoss hvSecond hcV hwhole

  let x : Fin n → Bool := flipBoolWordAt y d
  have hxQ :
      x ∈ retainedCompletionWords C v :=
    (mem_translatedCompletionWords C v d y).1 hyT
  have hsingle :
      IsSingleCompletionWord C v x :=
    projectedLoss_word_is_singleCompletionWord
      C exponent hexp honeLoss hvLoss hxQ
  have hyEq :
      flipBoolWordAt x d = y := by
    dsimp [x]
    exact flipBoolWordAt_involutive d y

  rcases single_flip_structural_transition C hsingle hdActive
    with hhole | hsingleNew | hoverlap
  · refine ⟨d,hdActive,hdc,Or.inl ?_⟩
    refine ⟨y,?_⟩
    simpa [x,hyEq] using hhole
  · right
    left
    obtain ⟨w,hwSingle,hwNe,hdW,hbitW⟩ := hsingleNew
    refine ⟨d,hdActive,hdc,Or.inr (Or.inl ?_)⟩
    refine ⟨y,w,?_,hwNe,hdW,hbitW⟩
    simpa [x,hyEq] using hwSingle
  · right
    right
    obtain ⟨u,w,huw,hres,huQ,hwQ,huNe,hwNe,
      hdU,hdW,hbitU,hbitW⟩ := hoverlap
    refine ⟨d,hdActive,hdc,Or.inr (Or.inr ?_)⟩
    refine ⟨y,u,w,huw,hres,?_,?_,huNe,hwNe,
      hdU,hdW,hbitU,hbitW⟩
    · simpa [x,hyEq] using huQ
    · simpa [x,hyEq] using hwQ

#print axioms wholeCube_offOwner_structural_transition

end OrderedEdgeColoring
end JSP000404Research
