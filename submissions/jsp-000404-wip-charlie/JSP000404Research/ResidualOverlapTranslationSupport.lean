import JSP000404Research.ResidualOverlapVaryingSupport
import JSP000404Research.ResidualReducedZeroOverlapTranslationQuotient
import Mathlib.Tactic

/-!
# Support invariance on the overlap-translation quotient

Coordinate translations preserve the set of coordinates that genuinely vary
inside an overlap set.  Since a nonempty retained-completion overlap cube has
varying-coordinate set exactly equal to its common retained-inactive support,
equality in the translation quotient forces equality of the full
common-inactive coordinate set, not merely equality of its cardinality.

This strengthens the stationary reduced-zero branch from a scalar rank tie to
a support-level rigidity statement.
-/

namespace JSP000404Research
namespace OrderedEdgeColoring

theorem oneFlipOverlapRel_varyingCoordinates_eq
    {n : ℕ}
    {S T : Finset (Fin n → Bool)}
    (h : oneFlipOverlapRel S T) :
    overlapVaryingCoordinates S =
      overlapVaryingCoordinates T := by
  rcases h with ⟨c,rfl⟩
  exact (overlapVaryingCoordinates_image_flip S c).symm

theorem overlapTranslationEquivalent_varyingCoordinates_eq
    {n : ℕ}
    {S T : Finset (Fin n → Bool)}
    (h : OverlapTranslationEquivalent S T) :
    overlapVaryingCoordinates S =
      overlapVaryingCoordinates T := by
  induction h with
  | rel _ _ hrel =>
      exact oneFlipOverlapRel_varyingCoordinates_eq hrel
  | refl _ =>
      rfl
  | symm _ _ _ ih =>
      exact ih.symm
  | trans _ _ _ _ _ ih₁ ih₂ =>
      exact ih₁.trans ih₂

theorem overlap_same_translation_quotient_commonRetainedInactive_eq
    {V : Type*} [LinearOrder V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    {u v w z : V}
    {baseUV baseWZ : Fin n → Bool}
    (huBase :
      baseUV ∈ retainedCompletionWords C u)
    (hvBase :
      baseUV ∈ retainedCompletionWords C v)
    (hwBase :
      baseWZ ∈ retainedCompletionWords C w)
    (hzBase :
      baseWZ ∈ retainedCompletionWords C z)
    (hq :
      Quotient.mk
          (overlapTranslationSetoid n)
          (retainedCompletionWords C u ∩
            retainedCompletionWords C v)
        =
      Quotient.mk
          (overlapTranslationSetoid n)
          (retainedCompletionWords C w ∩
            retainedCompletionWords C z)) :
    commonRetainedInactive C u v =
      commonRetainedInactive C w z := by
  have heqv :
      OverlapTranslationEquivalent
        (retainedCompletionWords C u ∩
          retainedCompletionWords C v)
        (retainedCompletionWords C w ∩
          retainedCompletionWords C z) := by
    exact Quotient.exact hq
  have hvary :=
    overlapTranslationEquivalent_varyingCoordinates_eq heqv
  rw [
    overlapVaryingCoordinates_eq_commonRetainedInactive
      C huBase hvBase,
    overlapVaryingCoordinates_eq_commonRetainedInactive
      C hwBase hzBase
  ] at hvary
  exact hvary

#print axioms oneFlipOverlapRel_varyingCoordinates_eq
#print axioms overlapTranslationEquivalent_varyingCoordinates_eq
#print axioms
  overlap_same_translation_quotient_commonRetainedInactive_eq

end OrderedEdgeColoring
end JSP000404Research
