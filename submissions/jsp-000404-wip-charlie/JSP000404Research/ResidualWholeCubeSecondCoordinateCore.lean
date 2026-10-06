import JSP000404Research.ResidualProjectedLossCore
import JSP000404Research.ResidualEnlargedCandidateCore
import JSP000404Research.TranslatedCompletionCore
import Mathlib.Tactic

/-!
# Lightweight whole-cube second-coordinate witness core

This file contains only the T/Q and T/T witness shapes used by local recursion
steps.  It deliberately excludes profile classification, Hall/minimal-core
machinery, and collision semantics.
-/

namespace JSP000404Research
namespace OrderedEdgeColoring

def WholeCubeSecondCoordinateSecondLayerWitness
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (T : Finset V)
    (s v : V) (c : Fin n) : Prop :=
  ∃ word : Fin n → Bool,
  ∃ w : V,
  ∃ d : Fin n,
    d ∈ retainedActive C v ∧
    d ≠ c ∧
    word ∈ translatedCompletionWords C v d ∧
    word ∈ enlargedProjectedCandidateBlock C exponent w ∧
    w ∈ T ∧
    w ≠ v ∧
    w ≠ s ∧
    w ∈ projectedLossVertices C exponent ∧
    exponent w = n - 2

def WholeCubeSecondCoordinateTQ
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (T : Finset V)
    (s v : V) (c : Fin n) : Prop :=
  ∃ word : Fin n → Bool,
  ∃ w : V,
  ∃ d : Fin n,
    d ∈ retainedActive C v ∧
    d ≠ c ∧
    word ∈ translatedCompletionWords C v d ∧
    word ∈ retainedCompletionWords C w ∧
    w ∈ T ∧
    w ≠ v ∧
    w ≠ s ∧
    w ∈ projectedLossVertices C exponent ∧
    exponent w = n - 2 ∧
    (
      (∃ hvw : v < w,
        ∃ hret : (C.color v w).val < n,
          retainedColor C v w hret = d)
      ∨
      (∃ hwv : w < v,
        ∃ hret : (C.color w v).val < n,
          retainedColor C w v hret = d)
    )

def WholeCubeSecondCoordinateTT
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (T : Finset V)
    (s v : V) (c : Fin n) : Prop :=
  ∃ word : Fin n → Bool,
  ∃ w : V,
  ∃ d e : Fin n,
    d ∈ retainedActive C v ∧
    d ≠ c ∧
    e ∈ retainedActive C w ∧
    e ≠ d ∧
    word ∈ translatedCompletionWords C v d ∧
    word ∈ translatedCompletionWords C w e ∧
    w ∈ T ∧
    w ≠ v ∧
    w ≠ s ∧
    w ∈ projectedLossVertices C exponent ∧
    exponent w = n - 2 ∧
    (
      (∃ hvw : v < w,
        ∃ hret : (C.color v w).val < n,
          retainedColor C v w hret = d ∨
          retainedColor C v w hret = e)
      ∨
      (∃ hwv : w < v,
        ∃ hret : (C.color w v).val < n,
          retainedColor C w v hret = d ∨
          retainedColor C w v hret = e)
    )

end OrderedEdgeColoring
end JSP000404Research
