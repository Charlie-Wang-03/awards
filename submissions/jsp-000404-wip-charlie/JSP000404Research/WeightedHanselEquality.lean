import JSP000404Research.WeightedHansel
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Tactic

/-!
# Equality rigidity for weighted Hansel partial cubes

The weighted Hansel proof is literally an injection

  Sigma v, FreeCoordinates(specified v) -> (Fin k -> Bool).

If the weighted Kraft sum attains 2^k, the domain and codomain have equal
finite cardinality.  The injection is therefore a bijection.

Consequently every Boolean word belongs to exactly one completed partial cube.
This is the correct combinatorial rigidity interface for equality terminals.
-/

namespace JSP000404Research

open scoped BigOperators

theorem completeWord_sigma_bijective_of_weight_eq
    {V : Type*} [Fintype V] {k : ℕ}
    (bit : V → Fin k → Bool)
    (specified : V → Finset (Fin k))
    (hsep : ∀ v w, v ≠ w → ∃ i,
      i ∈ specified v ∧ i ∈ specified w ∧ bit v i ≠ bit w i)
    (hweight :
      (∑ v, 2 ^ (k - (specified v).card)) = 2 ^ k) :
    Function.Bijective
      (fun x : Σ v, FreeCoordinates (specified v) =>
        completeWord bit specified x.1 x.2) := by
  let f :=
    fun x : Σ v, FreeCoordinates (specified v) =>
      completeWord bit specified x.1 x.2
  have hinj : Function.Injective f :=
    completeWord_sigma_injective bit specified hsep
  have hcard :
      Fintype.card (Σ v, FreeCoordinates (specified v)) =
        Fintype.card (Fin k → Bool) := by
    simpa [Fintype.card_sigma, card_freeCoordinates,
      Fintype.card_fun] using hweight
  exact
    (Fintype.bijective_iff_injective_and_card f).2
      ⟨hinj, hcard⟩

theorem completeWord_sigma_surjective_of_weight_eq
    {V : Type*} [Fintype V] {k : ℕ}
    (bit : V → Fin k → Bool)
    (specified : V → Finset (Fin k))
    (hsep : ∀ v w, v ≠ w → ∃ i,
      i ∈ specified v ∧ i ∈ specified w ∧ bit v i ≠ bit w i)
    (hweight :
      (∑ v, 2 ^ (k - (specified v).card)) = 2 ^ k) :
    Function.Surjective
      (fun x : Σ v, FreeCoordinates (specified v) =>
        completeWord bit specified x.1 x.2) :=
  (completeWord_sigma_bijective_of_weight_eq
    bit specified hsep hweight).2

theorem existsUnique_completion_of_weight_eq
    {V : Type*} [Fintype V] {k : ℕ}
    (bit : V → Fin k → Bool)
    (specified : V → Finset (Fin k))
    (hsep : ∀ v w, v ≠ w → ∃ i,
      i ∈ specified v ∧ i ∈ specified w ∧ bit v i ≠ bit w i)
    (hweight :
      (∑ v, 2 ^ (k - (specified v).card)) = 2 ^ k)
    (word : Fin k → Bool) :
    ∃! x : Σ v, FreeCoordinates (specified v),
      completeWord bit specified x.1 x.2 = word := by
  let f :=
    fun x : Σ v, FreeCoordinates (specified v) =>
      completeWord bit specified x.1 x.2
  have hbij :=
    completeWord_sigma_bijective_of_weight_eq
      bit specified hsep hweight
  obtain ⟨x, hx⟩ := hbij.2 word
  refine ⟨x, hx, ?_⟩
  intro y hy
  exact hbij.1 (hy.trans hx.symm)

#print axioms completeWord_sigma_bijective_of_weight_eq
#print axioms completeWord_sigma_surjective_of_weight_eq
#print axioms existsUnique_completion_of_weight_eq

end JSP000404Research
