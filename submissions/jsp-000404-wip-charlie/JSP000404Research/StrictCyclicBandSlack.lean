import JSP000404Research.CyclicBandGapDomination
import JSP000404Research.LocalGapGlobalCard
import JSP000404Research.StrictBandWeightedCapacity
import Mathlib.Tactic

/-!
# Strict cyclic floor slack is sufficient for the target dyadic capacity

At a centre, floor(real cyclic gaps) is componentwise dominated by
the cyclic jumps of the occupied integer bands. If the sum of
Sendov excesses is *strictly* smaller than that of the integer-band
jumps, the usual local n+1 budget improves to n.

Applied at every centre of an admissible DirectionData, this gives
the target 2^n weighted capacity via the strict-band Hansel theorem.

No claim is made that such a strict gap holds at every centre in an
arbitrary planar configuration; proving or replacing that condition is
a separate geometric task.
-/

namespace JSP000404Research

open scoped BigOperators

/-- The ordinary list of cyclic gap quotients is precisely the list of
natural floors of the cyclic real gaps. -/
theorem linearCyclicGapQuotients_eq_floor_cyclicRealGaps
    (t : ℝ) (angles : List ℝ) :
    linearCyclicGapQuotients t angles =
      (cyclicRealGapsAt t angles).map Nat.floor := by
  cases angles with
  | nil => rfl
  | cons a xs =>
      simp [linearCyclicGapQuotients, cyclicRealGapsAt,
        List.map_append]

/-- A strict floor-versus-band-jump exponent inequality improves the
integer unit-band budget from n+1 to n. -/
theorem cyclicFloorGapExponent_add_usedBands_le_n_of_strict
    (a : ℝ) (xs : List ℝ)
    {width : ℝ} (n : ℕ)
    (ha0 : 0 ≤ a)
    (hsorted : (a :: xs).Pairwise (· ≤ ·))
    (hall0 : ∀ x ∈ a :: xs, 0 ≤ x)
    (hallWidth : ∀ x ∈ a :: xs, x < width)
    (hwidth : width < (n : ℝ) + 1)
    (hstrict :
      listExponent
        ((cyclicRealGapsAt width (a :: xs)).map Nat.floor) <
      listExponent
        (cyclicBandJumps n ((a :: xs).map Nat.floor))) :
    listExponent
        ((cyclicRealGapsAt width (a :: xs)).map Nat.floor) +
      ((a :: xs).map Nat.floor).toFinset.card ≤ n := by
  have hlabelSorted :=
    floorLabels_pairwise a xs hsorted
  have hlabelBound :
      ∀ c ∈ (a :: xs).map Nat.floor, c ≤ n := by
    intro c hc
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hc
    exact floorLabel_le_n_of_lt_n_succ
      (hall0 x hx)
      ((hallWidth x hx).trans hwidth)
  have hbandCard :
      ((a :: xs).map Nat.floor).toFinset.card ≤ n + 1 := by
    have hsub :
        ((a :: xs).map Nat.floor).toFinset ⊆
          Finset.range (n + 1) := by
      intro c hc
      exact Finset.mem_range.mpr
        (Nat.lt_succ_of_le (hlabelBound c (List.mem_toFinset.mp hc)))
    have hcard := Finset.card_le_card hsub
    simpa using hcard
  have hBandExp :=
    cyclicBandJumps_exponent_eq_total_sub_distinct
      n (Nat.floor a) (xs.map Nat.floor)
      (by simpa only [List.map_cons] using hlabelSorted)
      (by
        intro c hc
        exact hlabelBound c (by simpa only [List.map_cons] using hc))
  simp only [List.map_cons] at hBandExp hstrict hbandCard ⊢
  rw [hBandExp] at hstrict
  omega

namespace DirectionData
namespace LocalDirectionCycle

/-- A strict cyclic floor inequality for an actual local direction cycle
produces one unit of extra unused standard-band capacity. -/
theorem exponent_add_incidentBands_card_le_n_of_strict
    {V : Type*} [LinearOrder V] [Fintype V]
    {t : ℝ} {n : ℕ}
    {D : DirectionData V t} {i : V}
    (C : LocalDirectionCycle D i)
    (ht : t < (n : ℝ) + 1)
    (hstrict :
      listExponent ((cyclicRealGapsAt t C.values).map Nat.floor) <
      listExponent (cyclicBandJumps n (C.values.map Nat.floor))) :
    C.exponent + (D.incidentBands (n + 1) i).card ≤ n := by
  obtain ⟨a, xs, hvalues⟩ :
      ∃ a xs, C.values = a :: xs := by
    cases h : C.values with
    | nil => exact False.elim (C.values_nonempty h)
    | cons a xs => exact ⟨a, xs, rfl⟩
  have hsorted :
      (a :: xs).Pairwise (· ≤ ·) := by
    simpa [hvalues] using C.values_pairwise
  have hall0 :
      ∀ x ∈ a :: xs, 0 ≤ x := by
    intro x hx
    exact (C.value_mem_bounds
      (by simpa [hvalues] using hx)).1
  have hallt :
      ∀ x ∈ a :: xs, x < t := by
    intro x hx
    exact (C.value_mem_bounds
      (by simpa [hvalues] using hx)).2
  have ha0 : 0 ≤ a := hall0 a (by simp)
  have hstrict' :
      listExponent ((cyclicRealGapsAt t (a :: xs)).map Nat.floor) <
      listExponent (cyclicBandJumps n ((a :: xs).map Nat.floor)) := by
    simpa [hvalues] using hstrict
  have hbudget :=
    cyclicFloorGapExponent_add_usedBands_le_n_of_strict
      a xs n ha0 hsorted hall0 hallt ht hstrict'
  have hexpEq :
      C.exponent =
        listExponent ((cyclicRealGapsAt t C.values).map Nat.floor) := by
    unfold LocalDirectionCycle.exponent LocalDirectionCycle.gapQuotients
    rw [linearCyclicGapQuotients_eq_floor_cyclicRealGaps]
  have hbudget' :
      C.exponent + (occupiedNatBands C.values).card ≤ n := by
    simpa only [hvalues, occupiedNatBands, hexpEq] using hbudget
  have ht' : t ≤ ((n + 1 : ℕ) : ℝ) := by
    have hx : t < ((n + 1 : ℕ) : ℝ) := by
      simpa [Nat.cast_add, Nat.cast_one] using ht
    exact le_of_lt hx
  have hcard :=
    C.occupiedNatBands_values_card_eq_incidentBands_card
      (n + 1) ht'
  rw [← hcard]
  exact hbudget'

end LocalDirectionCycle

/-- Entirely explicit sufficient condition on the actual cyclic directions
at all centres for the missing full Sendov 2^n weighted inequality. -/
theorem weighted_capacity_of_strict_cyclic_floor_slack
    {V : Type*} [LinearOrder V] [Fintype V]
    {t : ℝ} {n : ℕ}
    (D : DirectionData V t)
    (ht : t < (n : ℝ) + 1)
    (cycles : ∀ i : V, LocalDirectionCycle D i)
    (hstrict : ∀ i : V,
      listExponent
        ((cyclicRealGapsAt t (cycles i).values).map Nat.floor) <
      listExponent
        (cyclicBandJumps n ((cycles i).values.map Nat.floor))) :
    (∑ i : V, 2 ^ (cycles i).exponent) ≤ 2 ^ n := by
  have hlocal : ∀ i : V,
      (cycles i).exponent +
        (D.incidentBands (n + 1) i).card ≤ n := by
    intro i
    exact (cycles i).exponent_add_incidentBands_card_le_n_of_strict
      ht (hstrict i)
  exact weighted_capacity_of_strict_local_direction_cycles
    D ht cycles hlocal

#print axioms linearCyclicGapQuotients_eq_floor_cyclicRealGaps
#print axioms cyclicFloorGapExponent_add_usedBands_le_n_of_strict
#print axioms LocalDirectionCycle.exponent_add_incidentBands_card_le_n_of_strict
#print axioms weighted_capacity_of_strict_cyclic_floor_slack

end DirectionData
end JSP000404Research
