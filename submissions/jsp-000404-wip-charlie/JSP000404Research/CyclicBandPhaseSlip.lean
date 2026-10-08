import JSP000404Research.CyclicBandUnitJumpNecessity
import Mathlib.Tactic

/-!
# Saturation forces a short gap across an integer band boundary

At a saturated local centre the real cyclic-gap floor quotients q_j
are dominated by the integer band jumps b_j. Every b_j >= 2
must satisfy q_j = b_j. Since sum(q_j) < sum(b_j), there must
be a genuine phase-slip coordinate with (q_j,b_j) = (0,1).

This identifies a *specific* source of floor loss at a saturated
centre, rather than merely detecting some unit band jump.

The statement is necessary for overweight configurations, and
does not exclude such configurations on its own.
-/

namespace JSP000404Research

/-- Under large-jump rigidity, the only possible unequal
pair of corresponding quotient and band jump is (0,1). -/
theorem list_eq_of_large_rigid_without_phase_slip
    {qs bs : List ℕ}
    (hle : List.Forall₂ (· ≤ ·) qs bs)
    (hrigid : List.Forall₂ (fun q b => 2 ≤ b → q = b) qs bs)
    (hno : (0, 1) ∉ List.zip qs bs) : qs = bs := by
  induction hle with
  | nil => rfl
  | @cons q b qs bs hqb htail ih =>
      cases hrigid with
      | cons hlarge hrTail =>
          have hnoHead : ¬(q = 0 ∧ b = 1) := by
            rintro ⟨hq, hb⟩
            apply hno
            simp [List.zip, hq, hb]
          have hqbEq : q = b := by
            by_cases hb0 : b = 0
            · omega
            by_cases hb1 : b = 1
            · have hq1 : q ≤ 1 := by omega
              have hqne : q ≠ 0 := by
                intro hq0
                exact hnoHead ⟨hq0, hb1⟩
              omega
            · have hbLarge : 2 ≤ b := by omega
              exact hlarge hbLarge
          have hnoTail : (0, 1) ∉ List.zip qs bs := by
            intro hmem
            apply hno
            change (0, 1) ∈ (q, b) :: List.zip qs bs
            exact List.mem_cons_of_mem _ hmem
          exact congrArg₂ List.cons hqbEq (ih hrTail hnoTail)

/-- Equal Sendov excess combined with strict total quotient loss
forces a *zero-floor real gap* across a *unit band jump*. -/
theorem phase_slip_mem_zip_of_equal_exponent_and_sum_lt
    {qs bs : List ℕ}
    (hle : List.Forall₂ (· ≤ ·) qs bs)
    (hexp : listExponent qs = listExponent bs)
    (hsum : qs.sum < bs.sum) :
    (0, 1) ∈ List.zip qs bs := by
  by_contra hno
  have hr := forall₂_large_eq_of_le_and_listExponent_eq hle hexp
  have heq := list_eq_of_large_rigid_without_phase_slip hle hr hno
  rw [heq] at hsum
  exact (lt_irrefl _) hsum

namespace DirectionData
namespace LocalDirectionCycle

/-- A genuine local budget saturation necessarily contains a
paired cyclic gap/band jump (q,b)=(0,1). Thus a physical gap
shorter than one can straddle the unit-band boundary. -/
theorem has_floor_zero_unit_band_jump_of_local_tight
    {V : Type*} [LinearOrder V] [Fintype V]
    {t : ℝ} {n : ℕ}
    {D : DirectionData V t} {i : V}
    (C : LocalDirectionCycle D i)
    (ht : t < (n : ℝ) + 1)
    (htight :
      C.exponent + (D.incidentBands (n + 1) i).card = n + 1) :
    (0, 1) ∈ List.zip
      ((cyclicRealGapsAt t C.values).map Nat.floor)
      (cyclicBandJumps n (C.values.map Nat.floor)) := by
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
  have hcomp : List.Forall₂ (· ≤ ·)
      ((cyclicRealGapsAt t C.values).map Nat.floor)
      (cyclicBandJumps n (C.values.map Nat.floor)) := by
    simpa only [hvalues] using
      (cyclicFloorGaps_le_cyclicBandJumps
        a xs n ha0 hsorted hall ht)
  have hr :=
    C.large_band_jumps_floor_exact_of_local_tight ht htight
  have hfloorSum :
      ((cyclicRealGapsAt t C.values).map Nat.floor).sum ≤ n := by
    rw [hvalues]
    exact cyclicFloorGaps_sum_le_n
      t a xs n ha0 hsorted hall ht
  have hsortedNat := floorLabels_pairwise a xs hsorted
  have hlabels : ∀ c ∈ (a :: xs).map Nat.floor, c ≤ n := by
    intro c hc
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hc
    exact floorLabel_le_n_of_lt_n_succ
      (hall0 x hx) ((hall x hx).trans ht)
  have hbandSum :
      (cyclicBandJumps n (C.values.map Nat.floor)).sum = n + 1 := by
    rw [hvalues]
    simpa using (cyclicBandJumps_sum n (Nat.floor a) (xs.map Nat.floor)
      (by simpa using hsortedNat)
      (by
        intro c hc
        exact hlabels c (by simpa using hc)))
  have hsum :
      ((cyclicRealGapsAt t C.values).map Nat.floor).sum <
        (cyclicBandJumps n (C.values.map Nat.floor)).sum := by
    omega
  by_contra hno
  have heq := list_eq_of_large_rigid_without_phase_slip hcomp hr hno
  rw [heq] at hsum
  exact (lt_irrefl _) hsum

end LocalDirectionCycle

/-- A hypothetical overweight weighted Sendov profile must exhibit
a zero-floor cyclic gap paired with a unit integer-band jump at
some saturated centre. -/
theorem overweight_exists_phase_slip_centre
    {V : Type*} [LinearOrder V] [Fintype V]
    {t : ℝ} {n : ℕ}
    (D : DirectionData V t)
    (ht : t < (n : ℝ) + 1)
    (cycles : ∀ i : V, LocalDirectionCycle D i)
    (hover : 2 ^ n < ∑ i : V, 2 ^ (cycles i).exponent) :
    ∃ i : V,
      (0, 1) ∈ List.zip
        ((cyclicRealGapsAt t (cycles i).values).map Nat.floor)
        (cyclicBandJumps n ((cycles i).values.map Nat.floor)) := by
  obtain ⟨i, htight⟩ :=
    overweight_exists_tight_local_band_centre D ht cycles hover
  exact ⟨i, (cycles i).has_floor_zero_unit_band_jump_of_local_tight ht htight⟩

#print axioms list_eq_of_large_rigid_without_phase_slip
#print axioms phase_slip_mem_zip_of_equal_exponent_and_sum_lt
#print axioms LocalDirectionCycle.has_floor_zero_unit_band_jump_of_local_tight
#print axioms overweight_exists_phase_slip_centre

end DirectionData
end JSP000404Research
