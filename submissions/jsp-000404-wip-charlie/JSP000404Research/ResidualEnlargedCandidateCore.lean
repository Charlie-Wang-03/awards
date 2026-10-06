import JSP000404Research.ResidualProjectedLossCore
import JSP000404Research.TranslatedCompletionCore
import Mathlib.Tactic

/-!
# Lightweight enlarged projected candidate definitions

Only the Boolean set definitions are kept here.  Cardinality, slack, Hall and
minimal-deficiency arguments live in heavier modules.
-/

namespace JSP000404Research
namespace OrderedEdgeColoring

noncomputable def allActiveTranslatedWords
    {V : Type*} [LinearOrder V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (v : V) : Finset (Fin n → Bool) := by
  classical
  exact (retainedActive C v).biUnion
    (fun c => translatedCompletionWords C v c)

noncomputable def allActiveLossCandidateBlock
    {V : Type*} [LinearOrder V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (v : V) : Finset (Fin n → Bool) :=
  retainedCompletionWords C v ∪
    allActiveTranslatedWords C v

noncomputable def enlargedProjectedCandidateBlock
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (v : V) : Finset (Fin n → Bool) := by
  classical
  exact if v ∈ projectedLossVertices C exponent then
    allActiveLossCandidateBlock C v
  else
    retainedCompletionWords C v

theorem enlargedProjectedCandidateBlock_loss
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    {v : V}
    (hv : v ∈ projectedLossVertices C exponent) :
    enlargedProjectedCandidateBlock C exponent v =
      allActiveLossCandidateBlock C v := by
  classical
  simp [enlargedProjectedCandidateBlock, hv]

theorem enlargedProjectedCandidateBlock_nonloss
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    {v : V}
    (hv : v ∉ projectedLossVertices C exponent) :
    enlargedProjectedCandidateBlock C exponent v =
      retainedCompletionWords C v := by
  classical
  simp [enlargedProjectedCandidateBlock, hv]

#print axioms enlargedProjectedCandidateBlock_loss
#print axioms enlargedProjectedCandidateBlock_nonloss

end OrderedEdgeColoring
end JSP000404Research
