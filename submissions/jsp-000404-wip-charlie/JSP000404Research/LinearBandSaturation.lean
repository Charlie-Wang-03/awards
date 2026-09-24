
import JSP000404Research.LinearBandGapCapacity
import JSP000404Research.ResidualSaturationBridge
import JSP000404Research.StandardResidual
import Mathlib.Tactic

/-!
# Equality structure in the one-dimensional full-band inequality

The proof of LinearBandGapCapacity is the sum of two independent estimates:

  interior gap exponent + occupied bands
    <= floor(last)-floor(first)+1,

and

  wrap-gap excess
    <= n-floor(last)+floor(first).

The right-hand sides add to n+1.

Therefore if the full inequality is saturated, both component estimates are
saturated separately.

If the top band n is occupied, sortedness forces floor(last)=n, and the wrap
identity simplifies to

  wrap-gap excess = floor(first).

This gives concrete arithmetic rigidity for any saturated residual endpoint.
-/

namespace JSP000404Research

open Real

theorem floor_getLastD_eq_n_of_sorted_occupied_n
    {t : ℝ} {n : ℕ}
    (a : ℝ) (xs : List ℝ)
    (ha0 : 0 ≤ a)
    (hsorted : (a :: xs).Pairwise (· ≤ ·))
    (hall : ∀ x ∈ a :: xs, x < t)
    (ht : t < (n : ℝ) + 1)
    (hnOcc : n ∈ occupiedNatBands (a :: xs)) :
    Nat.floor (xs.getLastD a) = n := by
  have hlast0 :
      0 ≤ xs.getLastD a :=
    ha0.trans
      (head_le_getLastD_of_pairwise a xs hsorted)
  have hlastLe :
      Nat.floor (xs.getLastD a) ≤ n := by
    have hlt :
        xs.getLastD a < ((n + 1 : ℕ) : ℝ) := by
      have hz := hall _ (List.getLastD_mem_cons a xs)
      push_cast
      linarith
    have hf :
        Nat.floor (xs.getLastD a) < n + 1 :=
      (Nat.floor_lt hlast0).2 hlt
    omega
  rw [occupiedNatBands, List.mem_toFinset,
      List.mem_map] at hnOcc
  obtain ⟨x, hx, hfloorx⟩ := hnOcc
  have hheadLast :
      x ≤ xs.getLastD a := by
    simp only [List.mem_cons] at hx
    rcases hx with rfl | hx
    · exact head_le_getLastD_of_pairwise a xs hsorted
    · cases xs with
      | nil => simp at hx
      | cons b bs =>
          have htail :
              (b :: bs).Pairwise (· ≤ ·) :=
            (List.pairwise_cons.mp hsorted).2
          have hxTail : x ∈ b :: bs := by
            simpa using hx
          have hxle :
              x ≤ (bs.getLastD b) := by
            rcases List.mem_cons.mp hxTail with rfl | hxRest
            · exact head_le_getLastD_of_pairwise
                b bs htail
            · have hpairLast :
                  x ≤ bs.getLastD b := by
                have hlastMem :
                    bs.getLastD b ∈ b :: bs :=
                  List.getLastD_mem_cons b bs
                have hforall :=
                  htail.forall_of_forall
                    (fun _ _ h => h)
                exact hforall x hxTail
                  (bs.getLastD b) hlastMem
            exact hpairLast
          simpa [List.getLastD_cons] using hxle
  have hfloorLe :
      n ≤ Nat.floor (xs.getLastD a) := by
    rw [← hfloorx]
    exact Nat.floor_mono hheadLast
  omega

/-- Saturation of the total full-band inequality forces equality in the
interior and wrap estimates separately. -/
theorem linear_cyclic_saturation_component_equalities
    {t : ℝ} {n : ℕ}
    (a : ℝ) (xs : List ℝ)
    (ha0 : 0 ≤ a)
    (hsorted : (a :: xs).Pairwise (· ≤ ·))
    (hall : ∀ x ∈ a :: xs, x < t)
    (ht : t < (n : ℝ) + 1)
    (hsat :
      listExponent (linearCyclicGapQuotients t (a :: xs)) +
          (occupiedNatBands (a :: xs)).card
        =
      n + 1) :
    let z := xs.getLastD a
    let interior :=
      listExponent
        ((successiveDiffsFrom a xs).map Nat.floor)
    let wrap :=
      excess (Nat.floor (a + t - z))
    interior + (occupiedNatBands (a :: xs)).card =
        Nat.floor z - Nat.floor a + 1
    ∧
    wrap =
      n - Nat.floor z + Nat.floor a := by
  dsimp
  have haz :
      a ≤ xs.getLastD a :=
    head_le_getLastD_of_pairwise a xs hsorted
  have hinterior :=
    interior_gapExponent_add_occupied_le_span
      a xs ha0 hsorted
  have hwrap :=
    wrap_gap_excess_le_outer_empty_band_count
      ha0 haz
      (hall _ (List.getLastD_mem_cons a xs))
      ht
  have hfloorAZ :=
    floor_head_le_floor_getLastD_of_pairwise
      a xs hsorted
  have hlast0 : 0 ≤ xs.getLastD a :=
    ha0.trans haz
  have hlastN :
      Nat.floor (xs.getLastD a) ≤ n := by
    have hlt :
        xs.getLastD a < ((n + 1 : ℕ) : ℝ) := by
      have hz := hall _ (List.getLastD_mem_cons a xs)
      push_cast
      linarith
    have hf :
        Nat.floor (xs.getLastD a) < n + 1 :=
      (Nat.floor_lt hlast0).2 hlt
    omega
  have hsum :
      listExponent
          ((successiveDiffsFrom a xs).map Nat.floor) +
        excess (Nat.floor (a + t - xs.getLastD a)) +
        (occupiedNatBands (a :: xs)).card
      =
      n + 1 := by
    simpa [linearCyclicGapQuotients,
      listExponent_append, listExponent_singleton,
      add_assoc, add_left_comm, add_comm] using hsat
  constructor <;> omega

/-- If top band n is occupied, saturation makes the wrap exponent exactly the
first occupied floor. -/
theorem linear_cyclic_saturation_wrap_eq_firstFloor_of_top_occupied
    {t : ℝ} {n : ℕ}
    (a : ℝ) (xs : List ℝ)
    (ha0 : 0 ≤ a)
    (hsorted : (a :: xs).Pairwise (· ≤ ·))
    (hall : ∀ x ∈ a :: xs, x < t)
    (ht : t < (n : ℝ) + 1)
    (hnOcc : n ∈ occupiedNatBands (a :: xs))
    (hsat :
      listExponent (linearCyclicGapQuotients t (a :: xs)) +
          (occupiedNatBands (a :: xs)).card
        =
      n + 1) :
    excess
      (Nat.floor
        (a + t - xs.getLastD a))
      =
    Nat.floor a := by
  have hlast :=
    floor_getLastD_eq_n_of_sorted_occupied_n
      a xs ha0 hsorted hall ht hnOcc
  have hcomp :=
    linear_cyclic_saturation_component_equalities
      a xs ha0 hsorted hall ht hsat
  dsimp at hcomp
  rw [hlast] at hcomp
  have hfaLe :
      Nat.floor a ≤ n :=
    (Nat.floor_mono
      (head_le_getLastD_of_pairwise a xs hsorted)).trans_eq hlast
  omega

#print axioms floor_getLastD_eq_n_of_sorted_occupied_n
#print axioms linear_cyclic_saturation_component_equalities
#print axioms linear_cyclic_saturation_wrap_eq_firstFloor_of_top_occupied

end JSP000404Research
