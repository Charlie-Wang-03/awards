
import JSP000404Research.LinearBandGapCapacity
import Mathlib.Tactic

/-!
# Equality rigidity for the linear cyclic band-gap inequality

LinearBandGapCapacity proves

  gapExponent + occupiedBandCount <= n+1

for a sorted nonempty list of local normalized directions in [0,t), t<n+1.

When equality holds, the proof has only two nonnegative slack sources:

* the interior gaps versus the integer span from the first occupied band to
  the last;
* the cyclic wrap gap versus the unit bands outside that span.

Therefore global equality forces equality in both pieces separately.

This is the first rigidity statement needed for projected-budget saturated
vertices.
-/

namespace JSP000404Research

open Real

/-- Global equality splits into exact interior and wrap equalities. -/
theorem linear_cyclic_gapEquality_splits
    {t : ℝ} {n : ℕ}
    (a : ℝ) (xs : List ℝ)
    (ha0 : 0 ≤ a)
    (hsorted : (a :: xs).Pairwise (· ≤ ·))
    (hall : ∀ x ∈ a :: xs, x < t)
    (ht : t < (n : ℝ) + 1)
    (heq :
      listExponent (linearCyclicGapQuotients t (a :: xs)) +
          (occupiedNatBands (a :: xs)).card
        =
      n + 1) :
    (
      listExponent
          ((successiveDiffsFrom a xs).map Nat.floor) +
          (occupiedNatBands (a :: xs)).card
        =
      Nat.floor (xs.getLastD a) - Nat.floor a + 1
    )
    ∧
    (
      excess (Nat.floor (a + t - xs.getLastD a))
        =
      n - Nat.floor (xs.getLastD a) + Nat.floor a
    ) := by
  have hlast :
      xs.getLastD a < t :=
    hall _ (List.getLastD_mem_cons a xs)
  have haz :
      a ≤ xs.getLastD a :=
    head_le_getLastD_of_pairwise a xs hsorted
  have hinterior :=
    interior_gapExponent_add_occupied_le_span
      a xs ha0 hsorted
  have hwrap :=
    wrap_gap_excess_le_outer_empty_band_count
      ha0 haz hlast ht
  have hfloorAZ :
      Nat.floor a ≤ Nat.floor (xs.getLastD a) :=
    floor_head_le_floor_getLastD_of_pairwise
      a xs hsorted
  have hlast0 : 0 ≤ xs.getLastD a :=
    ha0.trans haz
  have hlastN :
      Nat.floor (xs.getLastD a) ≤ n := by
    have hlt :
        xs.getLastD a < ((n + 1 : ℕ) : ℝ) := by
      push_cast
      linarith
    have hf :
        Nat.floor (xs.getLastD a) < n + 1 :=
      (Nat.floor_lt hlast0).2 hlt
    omega
  have hsum :
      (Nat.floor (xs.getLastD a) - Nat.floor a + 1) +
        (n - Nat.floor (xs.getLastD a) + Nat.floor a)
        =
      n + 1 := by
    omega
  simp only [linearCyclicGapQuotients,
    listExponent_append, listExponent_singleton] at heq
  constructor <;> omega

/-- In particular, equality determines the wrap-gap excess exactly. -/
theorem wrap_gap_excess_eq_outer_empty_of_global_equality
    {t : ℝ} {n : ℕ}
    (a : ℝ) (xs : List ℝ)
    (ha0 : 0 ≤ a)
    (hsorted : (a :: xs).Pairwise (· ≤ ·))
    (hall : ∀ x ∈ a :: xs, x < t)
    (ht : t < (n : ℝ) + 1)
    (heq :
      listExponent (linearCyclicGapQuotients t (a :: xs)) +
          (occupiedNatBands (a :: xs)).card
        =
      n + 1) :
    excess (Nat.floor (a + t - xs.getLastD a))
      =
    n - Nat.floor (xs.getLastD a) + Nat.floor a :=
  (linear_cyclic_gapEquality_splits
    a xs ha0 hsorted hall ht heq).2

/-- If the last occupied band is the top band n, equality simplifies the wrap
excess to the index of the first occupied band. -/
theorem wrap_gap_excess_eq_floor_head_of_global_equality_top_last
    {t : ℝ} {n : ℕ}
    (a : ℝ) (xs : List ℝ)
    (ha0 : 0 ≤ a)
    (hsorted : (a :: xs).Pairwise (· ≤ ·))
    (hall : ∀ x ∈ a :: xs, x < t)
    (ht : t < (n : ℝ) + 1)
    (heq :
      listExponent (linearCyclicGapQuotients t (a :: xs)) +
          (occupiedNatBands (a :: xs)).card
        =
      n + 1)
    (hlast :
      Nat.floor (xs.getLastD a) = n) :
    excess (Nat.floor (a + t - xs.getLastD a)) =
      Nat.floor a := by
  have h :=
    wrap_gap_excess_eq_outer_empty_of_global_equality
      a xs ha0 hsorted hall ht heq
  rw [hlast] at h
  simpa using h

#print axioms linear_cyclic_gapEquality_splits
#print axioms wrap_gap_excess_eq_outer_empty_of_global_equality
#print axioms wrap_gap_excess_eq_floor_head_of_global_equality_top_last

end JSP000404Research
