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

theorem pointwise_eq_of_sum_eq_of_le
    {V : Type*} [Fintype V]
    (f g : V → ℕ)
    (hle : ∀ v, f v ≤ g v)
    (hsum : (∑ v, f v) = ∑ v, g v) :
    ∀ v, f v = g v := by
  classical
  intro v
  by_contra hne
  have hvlt : f v < g v :=
    lt_of_le_of_ne (hle v) hne
  have hrest :
      (∑ w ∈ (Finset.univ.erase v), f w) ≤
        ∑ w ∈ (Finset.univ.erase v), g w := by
    exact Finset.sum_le_sum
      (fun w _ => hle w)
  have hf :
      (∑ w : V, f w) =
        f v + ∑ w ∈ (Finset.univ.erase v), f w := by
    rw [← Finset.sum_erase_add f (Finset.mem_univ v)]
    omega
  have hg :
      (∑ w : V, g w) =
        g v + ∑ w ∈ (Finset.univ.erase v), g w := by
    rw [← Finset.sum_erase_add g (Finset.mem_univ v)]
    omega
  rw [hf, hg] at hsum
  omega

/-- If prescribed active-coordinate upper bounds already have exact Kraft
mass 2^k, every local upper bound is forced to be an equality. -/
theorem specified_card_eq_target_of_expected_capacity_eq
    {V : Type*} [Fintype V] {k : ℕ}
    (bit : V → Fin k → Bool)
    (specified : V → Finset (Fin k))
    (ell : V → ℕ)
    (hsep : ∀ v w, v ≠ w → ∃ i,
      i ∈ specified v ∧ i ∈ specified w ∧ bit v i ≠ bit w i)
    (hell : ∀ v, ell v ≤ k)
    (hactive : ∀ v, (specified v).card ≤ ell v)
    (hexpected :
      (∑ v, 2 ^ (k - ell v)) = 2 ^ k) :
    ∀ v, (specified v).card = ell v := by
  have hterm :
      ∀ v,
        2 ^ (k - ell v) ≤
          2 ^ (k - (specified v).card) := by
    intro v
    apply Nat.pow_le_pow_right (by norm_num : 0 < 2)
    omega
  have hlower :
      2 ^ k ≤
        ∑ v, 2 ^ (k - (specified v).card) := by
    rw [← hexpected]
    exact Finset.sum_le_sum (fun v _ => hterm v)
  have hupper :=
    weighted_hansel bit specified hsep
  have hactual :
      (∑ v, 2 ^ (k - (specified v).card)) = 2 ^ k := by
    omega
  have hsumEq :
      (∑ v, 2 ^ (k - ell v)) =
        ∑ v, 2 ^ (k - (specified v).card) := by
    rw [hexpected, hactual]
  have hpoint :=
    pointwise_eq_of_sum_eq_of_le
      (fun v => 2 ^ (k - ell v))
      (fun v => 2 ^ (k - (specified v).card))
      hterm hsumEq
  intro v
  have hexpEq :
      k - ell v = k - (specified v).card :=
    Nat.pow_right_injective (by norm_num : 2 ≤ 2)
      (hpoint v)
  have hcardLe :
      (specified v).card ≤ k :=
    (hactive v).trans (hell v)
  have hellv := hell v
  have hactv := hactive v
  omega

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
