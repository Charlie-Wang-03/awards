import JSP000404Research.CyclicBandTightRigidity
import Mathlib.Tactic

/-!
# A unit band jump is necessary for local Sendov-budget saturation

The floor quotients of real cyclic gaps have sum strictly below the
sum n+1 of the cyclic integer band jumps. Equality of the Sendov
excesses, on the other hand, forces all jumps of size >= 2 to be
floor-exact. Any discrepancy must therefore pass through a jump of
size exactly one.

This is a necessary structural property of a saturated centre.
It does not exclude saturated centres and it is not the global
Sendov capacity theorem.
-/

namespace JSP000404Research

/-- Componentwise floor domination plus large-jump rigidity and the
absence of unit jumps forces equality of the whole lists. -/
theorem list_eq_of_large_rigid_without_unit
    {qs bs : List ℕ}
    (hle : List.Forall₂ (· ≤ ·) qs bs)
    (hrigid : List.Forall₂ (fun q b => 2 ≤ b → q = b) qs bs)
    (hno : 1 ∉ bs) : qs = bs := by
  induction hle with
  | nil =>
      rfl
  | @cons q b qs bs hqb htail ih =>
      cases hrigid with
      | cons hlarge hrTail =>
          have hbne : b ≠ 1 := by
            intro hb
            apply hno
            simp [hb]
          have hbCases : b = 0 ∨ 2 ≤ b := by omega
          have hqbEq : q = b := by
            rcases hbCases with hb0 | hbLarge
            · omega
            · exact hlarge hbLarge
          have hnoTail : 1 ∉ bs := by
            intro hmem
            exact hno (List.mem_cons_of_mem b hmem)
          exact congrArg₂ List.cons hqbEq (ih hrTail hnoTail)

/-- If the dominated quotient list has equal excess but smaller
ordinary sum, at least one integer band jump equals one. -/
theorem unit_jump_mem_of_equal_exponent_and_sum_lt
    {qs bs : List ℕ}
    (hle : List.Forall₂ (· ≤ ·) qs bs)
    (hexp : listExponent qs = listExponent bs)
    (hsum : qs.sum < bs.sum) : 1 ∈ bs := by
  by_contra hno
  have hr := forall₂_large_eq_of_le_and_listExponent_eq hle hexp
  have heq := list_eq_of_large_rigid_without_unit hle hr hno
  rw [heq] at hsum
  exact (lt_irrefl _) hsum

/-- The real cyclic gaps telescope to precisely the circle width. -/
theorem cyclicRealGapsAt_sum
    (width a : ℝ) (xs : List ℝ) :
    (cyclicRealGapsAt width (a :: xs)).sum = width := by
  simp only [cyclicRealGapsAt, List.sum_append, List.sum_singleton,
    successiveDiffsFrom_sum]
  ring

/-- Sorted nonnegative angles yield nonnegative real cyclic gaps. -/
theorem cyclicRealGapsAt_nonneg
    (width a : ℝ) (xs : List ℝ)
    (ha0 : 0 ≤ a)
    (hsorted : (a :: xs).Pairwise (· ≤ ·))
    (hall : ∀ x ∈ a :: xs, x < width) :
    ∀ g ∈ cyclicRealGapsAt width (a :: xs), 0 ≤ g := by
  intro g hg
  simp only [cyclicRealGapsAt, List.mem_append,
    List.mem_singleton] at hg
  rcases hg with hdiff | hwrap
  · exact successiveDiffsFrom_nonneg a xs hsorted g hdiff
  · subst g
    have hlast : xs.getLastD a < width :=
      hall _ List.getLastD_mem_cons
    linarith

/-- On a nonnegative real list, the sum of natural floors is no
greater than the real sum. -/
theorem natFloor_list_sum_cast_le
    (xs : List ℝ) :
    (∀ x ∈ xs, 0 ≤ x) →
      (((xs.map Nat.floor).sum : ℕ) : ℝ) ≤ xs.sum := by
  induction xs with
  | nil =>
      intro _
      simp
  | cons x xs ih =>
      intro hall
      have hx0 : 0 ≤ x := hall x (by simp)
      have htail : ∀ y ∈ xs, 0 ≤ y := by
        intro y hy
        exact hall y (by simp [hy])
      have hfloor := Nat.floor_le hx0
      have hsum := ih htail
      simpa only [List.map_cons, List.sum_cons, Nat.cast_add]
        using add_le_add hfloor hsum

/-- The sum of natural cyclic-gap quotients is at most n, because
the real gaps sum to a width strictly less than n+1. -/
theorem cyclicFloorGaps_sum_le_n
    (width a : ℝ) (xs : List ℝ) (n : ℕ)
    (ha0 : 0 ≤ a)
    (hsorted : (a :: xs).Pairwise (· ≤ ·))
    (hall : ∀ x ∈ a :: xs, x < width)
    (hwidth : width < (n : ℝ) + 1) :
    ((cyclicRealGapsAt width (a :: xs)).map Nat.floor).sum ≤ n := by
  have hfloor :=
    natFloor_list_sum_cast_le
      (cyclicRealGapsAt width (a :: xs))
      (cyclicRealGapsAt_nonneg width a xs ha0 hsorted hall)
  rw [cyclicRealGapsAt_sum] at hfloor
  have hlt :
      (((cyclicRealGapsAt width (a :: xs)).map Nat.floor).sum : ℝ) <
        ((n + 1 : ℕ) : ℝ) := by
    exact lt_of_le_of_lt hfloor (by
      simpa only [Nat.cast_add, Nat.cast_one] using hwidth)
  have hnat :
      ((cyclicRealGapsAt width (a :: xs)).map Nat.floor).sum <
        n + 1 := by
    exact_mod_cast hlt
  omega

/-- At an abstract saturated cyclic direction list, some integer
band jump is exactly one. -/
theorem cyclicBandJumps_unit_mem_of_exponent_tight
    (a : ℝ) (xs : List ℝ) {width : ℝ} (n : ℕ)
    (ha0 : 0 ≤ a)
    (hsorted : (a :: xs).Pairwise (· ≤ ·))
    (hall0 : ∀ x ∈ a :: xs, 0 ≤ x)
    (hall : ∀ x ∈ a :: xs, x < width)
    (hwidth : width < (n : ℝ) + 1)
    (htight :
      listExponent ((cyclicRealGapsAt width (a :: xs)).map Nat.floor)
      + ((a :: xs).map Nat.floor).toFinset.card = n + 1) :
    1 ∈ cyclicBandJumps n ((a :: xs).map Nat.floor) := by
  have hle :=
    cyclicFloorGaps_le_cyclicBandJumps
      a xs n ha0 hsorted hall hwidth
  have hsortedNat := floorLabels_pairwise a xs hsorted
  have hlabels : ∀ c ∈ (a :: xs).map Nat.floor, c ≤ n := by
    intro c hc
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hc
    exact floorLabel_le_n_of_lt_n_succ
      (hall0 x hx) ((hall x hx).trans hwidth)
  have hbands :=
    cyclicBandJumps_sum n (Nat.floor a) (xs.map Nat.floor)
      (by simpa using hsortedNat)
      (by
        intro c hc
        exact hlabels c (by simpa using hc))
  have hexpBands :=
    cyclicBandJumps_exponent_eq_total_sub_distinct
      n (Nat.floor a) (xs.map Nat.floor)
      (by simpa using hsortedNat)
      (by
        intro c hc
        exact hlabels c (by simpa using hc))
  have heqExp :
      listExponent
        ((cyclicRealGapsAt width (a :: xs)).map Nat.floor) =
      listExponent
        (cyclicBandJumps n ((a :: xs).map Nat.floor)) := by
    change listExponent
      (cyclicBandJumps n ((a :: xs).map Nat.floor)) =
        n + 1 - ((a :: xs).map Nat.floor).toFinset.card at hexpBands
    omega
  have hfloorSum :=
    cyclicFloorGaps_sum_le_n width a xs n ha0 hsorted hall hwidth
  have hsum :
      ((cyclicRealGapsAt width (a :: xs)).map Nat.floor).sum <
      (cyclicBandJumps n ((a :: xs).map Nat.floor)).sum := by
    change
      ((cyclicRealGapsAt width (a :: xs)).map Nat.floor).sum <
        (cyclicBandJumps n (Nat.floor a :: xs.map Nat.floor)).sum
    omega
  exact unit_jump_mem_of_equal_exponent_and_sum_lt
    hle heqExp hsum

namespace DirectionData
namespace LocalDirectionCycle

/-- Every locally saturated direction cycle has an adjacent
integer-band jump of size exactly one. -/
theorem has_unit_band_jump_of_local_tight
    {V : Type*} [LinearOrder V] [Fintype V]
    {t : ℝ} {n : ℕ}
    {D : DirectionData V t} {i : V}
    (C : LocalDirectionCycle D i)
    (ht : t < (n : ℝ) + 1)
    (htight :
      C.exponent + (D.incidentBands (n + 1) i).card = n + 1) :
    1 ∈ cyclicBandJumps n (C.values.map Nat.floor) := by
  obtain ⟨a, xs, hvalues⟩ :
      ∃ a xs, C.values = a :: xs := by
    cases h : C.values with
    | nil => exact False.elim (C.values_nonempty h)
    | cons a xs => exact ⟨a, xs, rfl⟩
  have hsorted : (a :: xs).Pairwise (· ≤ ·) := by
    simpa [hvalues] using C.values_pairwise
  have hall0 : ∀ x ∈ a :: xs, 0 ≤ x := by
    intro x hx
    exact (C.value_mem_bounds
      (by simpa [hvalues] using hx)).1
  have hall : ∀ x ∈ a :: xs, x < t := by
    intro x hx
    exact (C.value_mem_bounds
      (by simpa [hvalues] using hx)).2
  have ha0 : 0 ≤ a := hall0 a (by simp)
  have heqExp :
      C.exponent =
        listExponent ((cyclicRealGapsAt t C.values).map Nat.floor) := by
    unfold LocalDirectionCycle.exponent LocalDirectionCycle.gapQuotients
    rw [linearCyclicGapQuotients_eq_floor_cyclicRealGaps]
  have hwidth : t ≤ ((n + 1 : ℕ) : ℝ) := by
    have : t < ((n + 1 : ℕ) : ℝ) := by
      simpa [Nat.cast_add, Nat.cast_one] using ht
    exact le_of_lt this
  have hcard :=
    C.occupiedNatBands_values_card_eq_incidentBands_card
      (n + 1) hwidth
  have htight' :
      listExponent ((cyclicRealGapsAt t (a :: xs)).map Nat.floor) +
        ((a :: xs).map Nat.floor).toFinset.card = n + 1 := by
    rw [← hcard] at htight
    simpa [hvalues, occupiedNatBands, heqExp] using htight
  simpa only [hvalues] using
    (cyclicBandJumps_unit_mem_of_exponent_tight
      a xs n ha0 hsorted hall0 hall ht htight')

end LocalDirectionCycle

/-- Every hypothetical violation of weighted 2^n capacity exhibits
a genuine unit-band jump at a locally saturated centre. -/
theorem overweight_exists_unit_band_jump_centre
    {V : Type*} [LinearOrder V] [Fintype V]
    {t : ℝ} {n : ℕ}
    (D : DirectionData V t)
    (ht : t < (n : ℝ) + 1)
    (cycles : ∀ i : V, LocalDirectionCycle D i)
    (hover : 2 ^ n < ∑ i : V, 2 ^ (cycles i).exponent) :
    ∃ i : V,
      1 ∈ cyclicBandJumps n ((cycles i).values.map Nat.floor) := by
  obtain ⟨i, htight⟩ :=
    overweight_exists_tight_local_band_centre D ht cycles hover
  exact ⟨i, (cycles i).has_unit_band_jump_of_local_tight ht htight⟩

#print axioms list_eq_of_large_rigid_without_unit
#print axioms unit_jump_mem_of_equal_exponent_and_sum_lt
#print axioms cyclicRealGapsAt_sum
#print axioms cyclicFloorGaps_sum_le_n
#print axioms cyclicBandJumps_unit_mem_of_exponent_tight
#print axioms LocalDirectionCycle.has_unit_band_jump_of_local_tight
#print axioms overweight_exists_unit_band_jump_centre

end DirectionData
end JSP000404Research
