import Mathlib.Data.Fintype.Card
import Mathlib.Data.Finset.Card
import Mathlib.Tactic

/-!
A weighted Hansel / Erdos--Szekeres coding inequality.

This is the finite combinatorial engine behind the current JSP-000404
research route. It contains no geometry: a vertex specifies some Boolean
coordinates, and every two different vertices disagree on at least one
coordinate specified by both. The corresponding partial Boolean subcubes
are disjoint, so their cardinalities fit inside the full Boolean cube.

Historically this is the content of the weighted even-partition argument in
Erdos--Szekeres (1960), Lemma 4, rewritten as a partial-code statement.
-/

namespace JSP000404Research

open scoped BigOperators

/-- Boolean assignments on the coordinates not specified at a vertex. -/
abbrev FreeCoordinates {k : ℕ} (specified : Finset (Fin k)) :=
  {i : Fin k // i ∉ specified} → Bool

/-- Complete a partial Boolean word by freely filling its unspecified coordinates. -/
def completeWord {V : Type*} {k : ℕ}
    (bit : V → Fin k → Bool) (specified : V → Finset (Fin k))
    (v : V) (free : FreeCoordinates (specified v)) : Fin k → Bool :=
  fun i => if hi : i ∈ specified v then bit v i else free ⟨i, hi⟩

/-- Pairwise disagreement on a commonly specified coordinate makes the family
of completed partial words injective. -/
theorem completeWord_sigma_injective
    {V : Type*} [Fintype V] {k : ℕ}
    (bit : V → Fin k → Bool) (specified : V → Finset (Fin k))
    (hsep : ∀ v w, v ≠ w → ∃ i,
      i ∈ specified v ∧ i ∈ specified w ∧ bit v i ≠ bit w i) :
    Function.Injective
      (fun x : Σ v, FreeCoordinates (specified v) =>
        completeWord bit specified x.1 x.2) := by
  classical
  intro x y hxy
  have hv : x.1 = y.1 := by
    by_contra hvw
    obtain ⟨i, hvi, hwi, hbit⟩ := hsep x.1 y.1 hvw
    have hi := congrFun hxy i
    simp [completeWord, hvi, hwi] at hi
    exact hbit hi
  cases x with
  | mk vx fx =>
    cases y with
    | mk vy fy =>
      change vx = vy at hv
      subst vy
      congr
      funext i
      have hi := congrFun hxy i.1
      simpa [completeWord, i.2] using hi

/-- The number of free completions of a partial Boolean word. -/
theorem card_freeCoordinates {k : ℕ} (specified : Finset (Fin k)) :
    Fintype.card (FreeCoordinates specified) = 2 ^ (k - specified.card) := by
  classical
  rw [Fintype.card_fun]
  simp

/-- Weighted Hansel inequality in partial-code form. -/
theorem weighted_hansel
    {V : Type*} [Fintype V] {k : ℕ}
    (bit : V → Fin k → Bool) (specified : V → Finset (Fin k))
    (hsep : ∀ v w, v ≠ w → ∃ i,
      i ∈ specified v ∧ i ∈ specified w ∧ bit v i ≠ bit w i) :
    ∑ v, 2 ^ (k - (specified v).card) ≤ 2 ^ k := by
  classical
  have hinj := completeWord_sigma_injective bit specified hsep
  have hcard :
      Fintype.card (Σ v, FreeCoordinates (specified v)) ≤
        Fintype.card (Fin k → Bool) :=
    Fintype.card_le_of_injective _ hinj
  simpa [Fintype.card_sigma, card_freeCoordinates] using hcard

/-- Alias emphasizing the cardinality form used by the JSP-000404 reduction. -/
theorem weighted_hansel_cardinality
    {V : Type*} [Fintype V] {k : ℕ}
    (bit : V → Fin k → Bool) (specified : V → Finset (Fin k))
    (hsep : ∀ v w, v ≠ w → ∃ i,
      i ∈ specified v ∧ i ∈ specified w ∧ bit v i ≠ bit w i) :
    ∑ v, 2 ^ (k - (specified v).card) ≤ 2 ^ k :=
  weighted_hansel bit specified hsep

#print axioms completeWord_sigma_injective
#print axioms card_freeCoordinates
#print axioms weighted_hansel
#print axioms weighted_hansel_cardinality

end JSP000404Research
