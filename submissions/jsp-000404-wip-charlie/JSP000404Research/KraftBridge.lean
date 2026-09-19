import JSP000404Research.WeightedDefect

/-!
# Partial-cube certificate for the sharp Sendov capacity

This file isolates the exact finite combinatorial object still needed from
geometry.

For an ambient Boolean cube of dimension `k`, a vertex `v` with deficit
`ell v` should specify exactly `ell v` coordinates.  The remaining
`k - ell v` coordinates are free, so its partial word represents a subcube
of size `2^(k-ell v)`.

If every two different vertices disagree on one coordinate specified by both,
the represented subcubes are disjoint.  `weighted_hansel` then gives the
desired Kraft/capacity inequality immediately.
-/

namespace JSP000404Research

open scoped BigOperators

/-- The finite partial-code certificate which would close the lower Sendov
capacity branch once constructed from the ordered-direction geometry. -/
structure KraftCertificate (V : Type*) [Fintype V] (k : ℕ) (ell : V → ℕ) where
  bit : V → Fin k → Bool
  specified : V → Finset (Fin k)
  card_specified : ∀ v, (specified v).card = ell v
  separates : ∀ v w, v ≠ w → ∃ i,
    i ∈ specified v ∧ i ∈ specified w ∧ bit v i ≠ bit w i

/-- A Kraft certificate packs the corresponding partial Boolean subcubes into
the ambient cube. -/
theorem kraft_capacity_of_certificate
    {V : Type*} [Fintype V] {k : ℕ} {ell : V → ℕ}
    (C : KraftCertificate V k ell) :
    ∑ v, 2 ^ (k - ell v) ≤ 2 ^ k := by
  have h := weighted_hansel C.bit C.specified C.separates
  simpa only [C.card_specified] using h

/-- Defect form of the same certificate. -/
theorem kraft_defect_of_certificate
    {V : Type*} [Fintype V] {k : ℕ} {ell : V → ℕ}
    (C : KraftCertificate V k ell) :
    ∑ v, (2 ^ (k - ell v) - 1) ≤ 2 ^ k - Fintype.card V := by
  have h := weighted_hansel_defect C.bit C.specified C.separates
  simpa only [C.card_specified] using h

/-- If `ell v ≤ k`, the exponent `k - ell v` is exactly the cluster
exponent associated with deficit `ell v`.  This convenience lemma records
the arithmetic conversion used in the Sendov application. -/
theorem pow_deficit_eq {k exponent ell : ℕ}
    (hexponent : exponent ≤ k)
    (hell : ell = k - exponent) :
    2 ^ (k - ell) = 2 ^ exponent := by
  subst ell
  rw [Nat.sub_sub_cancel hexponent]

/-- Hence a certificate with `ell v = k - exponent v` directly bounds the
sum of the cluster weights `2^(exponent v)`. -/
theorem cluster_capacity_of_certificate
    {V : Type*} [Fintype V] {k : ℕ}
    (exponent ell : V → ℕ)
    (C : KraftCertificate V k ell)
    (hexponent : ∀ v, exponent v ≤ k)
    (hell : ∀ v, ell v = k - exponent v) :
    ∑ v, 2 ^ exponent v ≤ 2 ^ k := by
  have h := kraft_capacity_of_certificate C
  calc
    ∑ v, 2 ^ exponent v =
        ∑ v, 2 ^ (k - ell v) := by
          apply Finset.sum_congr rfl
          intro v _
          symm
          exact pow_deficit_eq (hexponent v) (hell v)
    _ ≤ 2 ^ k := h

#print axioms kraft_capacity_of_certificate
#print axioms kraft_defect_of_certificate
#print axioms pow_deficit_eq
#print axioms cluster_capacity_of_certificate

end JSP000404Research
