
import JSP000404Research.LinearBandGapCapacity
import JSP000404Research.LocalDirectionCycleCore
import JSP000404Research.OrderedBandCode
import JSP000404Research.FiniteProjectiveRays
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Prod.Lex
import Mathlib.Tactic

/-!
# Local cyclic direction data at one ordered vertex

For DirectionData D of width t and a fixed vertex i, every other vertex j
determines one incident unoriented line direction value:

* if j<i, use the forward edge value D.value j i;
* if i<j, use D.value i j.

All such values lie in [0,t).  Sort all non-centre vertices by this local value
(with the vertex itself as a deterministic tie-breaker), preserving
multiplicity.

The resulting LocalDirectionCycle is the DirectionData analogue of
CentreProjectiveCycle.

Its cyclic gap quotient list is obtained by flooring successive differences
and the wrap difference through circumference t.

LinearBandGapCapacity then gives the exact full-band inequality

  localDirectionExponent + card(incidentBands D (n+1) i) <= n+1

whenever t<n+1.

The only remaining geometric identification needed later is that, for the
generic planar DirectionData, this local cyclic exponent equals the canonical
centreExponent.
-/

namespace JSP000404Research
namespace DirectionData

theorem mem_incidentBands_iff_exists_local_floor
    {V : Type*} [LinearOrder V]
    {t : ℝ}
    (D : DirectionData V t)
    (k : ℕ)
    (i : V)
    (c : Fin k) :
    c ∈ D.incidentBands k i ↔
      ∃ j : OtherVertex i,
        Nat.floor (D.localDirectionValue i j) = c.val := by
  classical
  simp only [incidentBands, Finset.mem_filter,
    Finset.mem_univ, true_and]
  constructor
  · intro h
    rcases h with hin | hout
    · obtain ⟨w, hwi, hlo, hhi⟩ := hin
      let j : OtherVertex i := ⟨w, ne_of_lt hwi⟩
      refine ⟨j, ?_⟩
      have hx0 := D.nonnegative hwi
      have hf :
          Nat.floor (D.value w i) = c.val :=
        (Nat.floor_eq_iff hx0).2 (by
          simpa using And.intro hlo hhi)
      simpa [localDirectionValue, j, hwi] using hf
    · obtain ⟨w, hiw, hlo, hhi⟩ := hout
      let j : OtherVertex i := ⟨w, ne_of_gt hiw⟩
      refine ⟨j, ?_⟩
      have hx0 := D.nonnegative hiw
      have hf :
          Nat.floor (D.value i w) = c.val :=
        (Nat.floor_eq_iff hx0).2 (by
          simpa using And.intro hlo hhi)
      have hnwi : ¬ w < i := not_lt_of_ge hiw.le
      simpa [localDirectionValue, j, hnwi] using hf
  · rintro ⟨j, hjfloor⟩
    by_cases hji : j.1 < i
    · have hx0 := D.nonnegative hji
      have hlo := Nat.floor_le hx0
      have hhi := Nat.lt_floor_add_one (D.value j.1 i)
      have hloc :
          D.localDirectionValue i j = D.value j.1 i := by
        simp [localDirectionValue, hji]
      rw [hloc] at hjfloor
      have hcast :
          ((Nat.floor (D.value j.1 i) : ℕ) : ℝ) = (c.val : ℝ) := by
        exact_mod_cast hjfloor
      rw [hcast] at hlo hhi
      exact Or.inl ⟨j.1, hji, hlo, hhi⟩
    · have hij : i < j.1 := by
        have hle : i ≤ j.1 := le_of_not_gt hji
        exact lt_of_le_of_ne hle j.2.symm
      have hx0 := D.nonnegative hij
      have hlo := Nat.floor_le hx0
      have hhi := Nat.lt_floor_add_one (D.value i j.1)
      have hloc :
          D.localDirectionValue i j = D.value i j.1 := by
        simp [localDirectionValue, hji]
      rw [hloc] at hjfloor
      have hcast :
          ((Nat.floor (D.value i j.1) : ℕ) : ℝ) = (c.val : ℝ) := by
        exact_mod_cast hjfloor
      rw [hcast] at hlo hhi
      exact Or.inr ⟨j.1, hij, hlo, hhi⟩

/-- The natural floors appearing in a complete local direction cycle are
exactly the values of the incident Fin k band set. -/
theorem occupiedNatBands_values_eq_incident_val_map
    {V : Type*} [LinearOrder V] [Fintype V]
    {t : ℝ}
    {D : DirectionData V t} {i : V}
    (C : LocalDirectionCycle D i)
    (k : ℕ)
    (hwidth : t ≤ (k : ℝ)) :
    occupiedNatBands C.values =
      (D.incidentBands k i).map Fin.valEmbedding := by
  classical
  ext m
  constructor
  · intro hm
    rw [occupiedNatBands, List.mem_toFinset,
        List.mem_map] at hm
    obtain ⟨x, hx, hfloor⟩ := hm
    rw [values, List.mem_map] at hx
    obtain ⟨j, hj, rfl⟩ := hx
    have hlt :
        Nat.floor (D.localDirectionValue i j) < k := by
      have hx0 := D.localDirectionValue_nonneg i j
      have hxk :
          D.localDirectionValue i j < (k : ℝ) :=
        (D.localDirectionValue_lt i j).trans_le hwidth
      exact (Nat.floor_lt hx0).2 hxk
    let c : Fin k :=
      ⟨Nat.floor (D.localDirectionValue i j), hlt⟩
    have hc :
        c ∈ D.incidentBands k i := by
      apply (mem_incidentBands_iff_exists_local_floor
        D k i c).2
      exact ⟨j, rfl⟩
    apply Finset.mem_map.mpr
    refine ⟨c, hc, ?_⟩
    simpa [c] using hfloor
  · intro hm
    obtain ⟨c, hc, hcm⟩ := Finset.mem_map.mp hm
    have hex :=
      (mem_incidentBands_iff_exists_local_floor
        D k i c).1 hc
    obtain ⟨j, hjfloor⟩ := hex
    have hj :
        j ∈ C.rays := by
      have : j ∈ C.rays.toFinset := by
        rw [C.complete]
        simp
      simpa using this
    rw [occupiedNatBands, List.mem_toFinset,
        List.mem_map]
    refine ⟨D.localDirectionValue i j, ?_, ?_⟩
    · rw [values, List.mem_map]
      exact ⟨j, hj, rfl⟩
    · have hval :
          c.val = m := by
        simpa using hcm
      rw [hjfloor, hval]

theorem occupiedNatBands_values_card_eq_incidentBands_card
    {V : Type*} [LinearOrder V] [Fintype V]
    {t : ℝ}
    {D : DirectionData V t} {i : V}
    (C : LocalDirectionCycle D i)
    (k : ℕ)
    (hwidth : t ≤ (k : ℝ)) :
    (occupiedNatBands C.values).card =
      (D.incidentBands k i).card := by
  rw [occupiedNatBands_values_eq_incident_val_map
    C k hwidth]
  simp

/-- Main local full-band inequality. -/
theorem exponent_add_incidentBands_card_le
    {V : Type*} [LinearOrder V] [Fintype V]
    {t : ℝ} {n : ℕ}
    {D : DirectionData V t} {i : V}
    (C : LocalDirectionCycle D i)
    (ht : t < (n : ℝ) + 1) :
    C.exponent + (D.incidentBands (n + 1) i).card ≤ n + 1 := by
  obtain ⟨a, xs, hvalues⟩ :
      ∃ a xs, C.values = a :: xs := by
    cases h : C.values with
    | nil =>
        exact False.elim (C.values_nonempty h)
    | cons a xs =>
        exact ⟨a, xs, rfl⟩
  have haMem : a ∈ C.values := by
    rw [hvalues]
    simp
  have ha0 := (C.value_mem_bounds haMem).1
  have hsorted :
      (a :: xs).Pairwise (· ≤ ·) := by
    simpa [hvalues] using C.values_pairwise
  have hall :
      ∀ x ∈ a :: xs, x < t := by
    intro x hx
    exact (C.value_mem_bounds
      (by simpa [hvalues] using hx)).2
  have hlin :=
    linear_cyclic_gapExponent_add_occupied_le
      a xs ha0 hsorted hall ht
  have hwidth :
      t ≤ ((n + 1 : ℕ) : ℝ) := by
    push_cast
    linarith
  have hcard :=
    C.occupiedNatBands_values_card_eq_incidentBands_card
      (n + 1) hwidth
  unfold exponent gapQuotients
  rw [hvalues, ← hcard, hvalues]
  exact hlin

#print axioms localDirectionValue_nonneg
#print axioms exists_localDirectionCycle
#print axioms mem_incidentBands_iff_exists_local_floor
#print axioms occupiedNatBands_values_eq_incident_val_map
#print axioms LocalDirectionCycle.exponent_add_incidentBands_card_le

end LocalDirectionCycle
end DirectionData
end JSP000404Research
