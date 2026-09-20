import JSP000404Research.LowDeficitSupport
import JSP000404Research.UniqueTransitionGap
import Mathlib.Data.List.OfFn
import Mathlib.Tactic

/-!
# Bridging finite quotient support to the transition-list support

The Sendov arithmetic modules represent one centre's quotient data as a finite
function q : Fin m -> Nat and use positiveSupport q.

The sign-transition modules use the aligned quotient list List.ofFn q and its
recursive listPositiveCount.

These are exactly the same count.  This file closes that representation gap,
so the large-exponent support bound can feed directly into the unique
transition-gap theorem.
-/

namespace JSP000404Research

/-- listPositiveCount of the canonical list representation is exactly the
finite-function positive support. -/
theorem listPositiveCount_ofFn_eq_positiveSupport
    {m : ℕ} (q : Fin m → ℕ) :
    listPositiveCount (List.ofFn q) = positiveSupport q := by
  induction m with
  | zero =>
      simp [listPositiveCount, positiveSupport]
  | succ m ih =>
      rw [List.ofFn_succ]
      unfold listPositiveCount positiveSupport
      rw [Fin.sum_univ_succ]
      have htail :=
        ih (fun i : Fin m => q i.succ)
      unfold positiveSupport at htail
      rw [htail]
      rfl

/-- Deficit at most two gives list support at most two. -/
theorem listPositiveCount_ofFn_le_two_of_deficit_le_two
    {m n : ℕ}
    (q : Fin m → ℕ)
    (hQ : (∑ i, q i) ≤ n)
    (hell : n - floorExcess q ≤ 2) :
    listPositiveCount (List.ofFn q) ≤ 2 := by
  rw [listPositiveCount_ofFn_eq_positiveSupport]
  exact positiveSupport_le_two_of_deficit_le_two q n hQ hell

/-- Top-three-layer exponent form. -/
theorem listPositiveCount_ofFn_le_two_of_large_exponent
    {m n k ell : ℕ}
    (q : Fin m → ℕ)
    (hQ : (∑ i, q i) ≤ n)
    (hk : k = floorExcess q)
    (hell : ell = n - k)
    (hlarge : n - 2 ≤ k) :
    listPositiveCount (List.ofFn q) ≤ 2 := by
  rw [listPositiveCount_ofFn_eq_positiveSupport]
  exact positiveSupport_le_two_of_large_exponent
    q n k ell hQ hk hell hlarge

/-- Therefore any antiperiodic sign path aligned with a large-exponent quotient
function has a unique transition carried by a positive quotient gap. -/
theorem large_exponent_has_positive_transition_gap
    {m n k ell : ℕ}
    (q : Fin m → ℕ)
    (hQ : (∑ i, q i) ≤ n)
    (hk : k = floorExcess q)
    (hell : ell = n - k)
    (hlarge : n - 2 ≤ k)
    (a : Bool) (signs : List Bool)
    (hchanges :
      ChangesOnlyOnPositive a signs (List.ofFn q))
    (hlast : boolLastFrom a signs = !a) :
    ∃ pre post : List ℕ, ∃ qe : ℕ,
      qe ≠ 0 ∧
      List.ofFn q = pre ++ qe :: post ∧
      signs =
        List.replicate pre.length a ++
          List.replicate (post.length + 1) (!a) := by
  apply antiperiodic_positive_transition_gap_of_support_le_two
    a signs (List.ofFn q) hchanges hlast
  exact listPositiveCount_ofFn_le_two_of_large_exponent
    q hQ hk hell hlarge

#print axioms listPositiveCount_ofFn_eq_positiveSupport
#print axioms listPositiveCount_ofFn_le_two_of_large_exponent
#print axioms large_exponent_has_positive_transition_gap

end JSP000404Research
