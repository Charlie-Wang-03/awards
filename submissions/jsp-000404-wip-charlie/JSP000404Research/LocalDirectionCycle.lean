
import JSP000404Research.LinearBandGapCapacity
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

def localDirectionValue
    {V : Type*} [LinearOrder V]
    {t : ℝ}
    (D : DirectionData V t)
    (i : V) (j : OtherVertex i) : ℝ :=
  if h : j.1 < i then
    D.value j.1 i
  else
    D.value i j.1

theorem localDirectionValue_nonneg
    {V : Type*} [LinearOrder V]
    {t : ℝ}
    (D : DirectionData V t)
    (i : V) (j : OtherVertex i) :
    0 ≤ D.localDirectionValue i j := by
  unfold localDirectionValue
  by_cases hji : j.1 < i
  · simp [hji, D.nonnegative hji]
  · have hij : i < j.1 := by
      have hle : i ≤ j.1 := le_of_not_gt hji
      exact lt_of_le_of_ne hle j.2.symm
    simp [hji, D.nonnegative hij]

theorem localDirectionValue_lt
    {V : Type*} [LinearOrder V]
    {t : ℝ}
    (D : DirectionData V t)
    (i : V) (j : OtherVertex i) :
    D.localDirectionValue i j < t := by
  unfold localDirectionValue
  by_cases hji : j.1 < i
  · simp [hji, D.belowWidth hji]
  · have hij : i < j.1 := by
      have hle : i ≤ j.1 := le_of_not_gt hji
      exact lt_of_le_of_ne hle j.2.symm
    simp [hji, D.belowWidth hij]

noncomputable def localDirectionOrderKey
    {V : Type*} [LinearOrder V]
    {t : ℝ}
    (D : DirectionData V t)
    (i : V) (j : OtherVertex i) :
    ℝ ×ₗ V :=
  toLex (D.localDirectionValue i j, j.1)

theorem localDirectionOrderKey_injective
    {V : Type*} [LinearOrder V]
    {t : ℝ}
    (D : DirectionData V t)
    (i : V) :
    Function.Injective (D.localDirectionOrderKey i) := by
  intro a b hab
  apply Subtype.ext
  have hsecond :
      (ofLex (D.localDirectionOrderKey i a)).2 =
        (ofLex (D.localDirectionOrderKey i b)).2 :=
    congrArg (fun z : ℝ ×ₗ V => (ofLex z).2) hab
  simpa [localDirectionOrderKey] using hsecond

noncomputable def localDirectionOrder
    {V : Type*} [LinearOrder V]
    {t : ℝ}
    (D : DirectionData V t)
    (i : V) :
    LinearOrder (OtherVertex i) :=
  LinearOrder.lift'
    (D.localDirectionOrderKey i)
    (D.localDirectionOrderKey_injective i)

theorem localDirectionValue_le_of_order_le
    {V : Type*} [LinearOrder V]
    {t : ℝ}
    (D : DirectionData V t)
    (i : V)
    {a b : OtherVertex i}
    (hab :
      @LE.le (OtherVertex i)
        (D.localDirectionOrder i).toLE a b) :
    D.localDirectionValue i a ≤
      D.localDirectionValue i b := by
  have hkey :
      D.localDirectionOrderKey i a ≤
        D.localDirectionOrderKey i b := hab
  have hfst := Prod.Lex.monotone_fst _ _ hkey
  simpa [localDirectionOrderKey] using hfst

structure LocalDirectionCycle
    {V : Type*} [LinearOrder V] [Fintype V]
    {t : ℝ}
    (D : DirectionData V t)
    (i : V) where
  rays : List (OtherVertex i)
  complete : rays.toFinset = Finset.univ
  nodup : rays.Nodup
  nonempty : rays ≠ []
  value_sorted :
    rays.Pairwise
      (fun a b =>
        D.localDirectionValue i a ≤
          D.localDirectionValue i b)

namespace LocalDirectionCycle

def values
    {V : Type*} [LinearOrder V] [Fintype V]
    {t : ℝ}
    {D : DirectionData V t} {i : V}
    (C : LocalDirectionCycle D i) : List ℝ :=
  C.rays.map (D.localDirectionValue i)

def gapQuotients
    {V : Type*} [LinearOrder V] [Fintype V]
    {t : ℝ}
    {D : DirectionData V t} {i : V}
    (C : LocalDirectionCycle D i) : List ℕ :=
  linearCyclicGapQuotients t C.values

def exponent
    {V : Type*} [LinearOrder V] [Fintype V]
    {t : ℝ}
    {D : DirectionData V t} {i : V}
    (C : LocalDirectionCycle D i) : ℕ :=
  listExponent C.gapQuotients

theorem values_nonempty
    {V : Type*} [LinearOrder V] [Fintype V]
    {t : ℝ}
    {D : DirectionData V t} {i : V}
    (C : LocalDirectionCycle D i) :
    C.values ≠ [] := by
  simp [values, C.nonempty]

theorem values_pairwise
    {V : Type*} [LinearOrder V] [Fintype V]
    {t : ℝ}
    {D : DirectionData V t} {i : V}
    (C : LocalDirectionCycle D i) :
    C.values.Pairwise (· ≤ ·) := by
  rw [values, List.pairwise_map]
  exact C.value_sorted

theorem value_mem_bounds
    {V : Type*} [LinearOrder V] [Fintype V]
    {t : ℝ}
    {D : DirectionData V t} {i : V}
    (C : LocalDirectionCycle D i)
    {x : ℝ}
    (hx : x ∈ C.values) :
    0 ≤ x ∧ x < t := by
  rw [values, List.mem_map] at hx
  obtain ⟨j, _, rfl⟩ := hx
  exact ⟨D.localDirectionValue_nonneg i j,
    D.localDirectionValue_lt i j⟩

theorem exists_localDirectionCycle
    {V : Type*} [LinearOrder V] [Fintype V]
    {t : ℝ}
    (D : DirectionData V t)
    (i : V)
    (hother : Nonempty (OtherVertex i)) :
    Nonempty (LocalDirectionCycle D i) := by
  classical
  letI : LinearOrder (OtherVertex i) :=
    D.localDirectionOrder i
  let rays : List (OtherVertex i) :=
    (Finset.univ : Finset (OtherVertex i)).sort
  have hne : rays ≠ [] := by
    obtain ⟨j⟩ := hother
    intro hr
    have hj :
        j ∈ (Finset.univ : Finset (OtherVertex i)) := by simp
    have hj' : j ∈ rays := by
      dsimp [rays]
      simpa using hj
    rw [hr] at hj'
    simp at hj'
  refine ⟨{
    rays := rays
    complete := ?_
    nodup := ?_
    nonempty := hne
    value_sorted := ?_ }⟩
  · dsimp [rays]
    simp
  · dsimp [rays]
    exact Finset.sort_nodup _ _
  · have hpair :
        rays.Pairwise
          (fun a b : OtherVertex i => a ≤ b) := by
      dsimp [rays]
      exact Finset.pairwise_sort _ _
    apply hpair.imp
    intro a b hab
    exact D.localDirectionValue_le_of_order_le i hab

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
    · left
      refine ⟨j.1, hji, ?_, ?_⟩
      have hx0 := D.nonnegative hji
      have hlo := Nat.floor_le hx0
      have hhi := Nat.lt_floor_add_one (D.value j.1 i)
      have hloc :
          D.localDirectionValue i j = D.value j.1 i := by
        simp [localDirectionValue, hji]
      rw [hloc] at hjfloor
      rw [hjfloor] at hlo hhi
      · simpa using hlo
      · simpa using hhi
    · have hij : i < j.1 := by
        have hle : i ≤ j.1 := le_of_not_gt hji
        exact lt_of_le_of_ne hle j.2.symm
      right
      refine ⟨j.1, hij, ?_, ?_⟩
      have hx0 := D.nonnegative hij
      have hlo := Nat.floor_le hx0
      have hhi := Nat.lt_floor_add_one (D.value i j.1)
      have hloc :
          D.localDirectionValue i j = D.value i j.1 := by
        simp [localDirectionValue, hji]
      rw [hloc] at hjfloor
      rw [hjfloor] at hlo hhi
      · simpa using hlo
      · simpa using hhi

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
    simpa [c] using hfloor.symm
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
        simpa using congrArg Fin.val hcm
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
        exact ⟨a, xs, h⟩
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
  rw [hvalues] at hlin
  rw [hcard] at hlin
  simpa using hlin

#print axioms localDirectionValue_nonneg
#print axioms exists_localDirectionCycle
#print axioms mem_incidentBands_iff_exists_local_floor
#print axioms occupiedNatBands_values_eq_incident_val_map
#print axioms LocalDirectionCycle.exponent_add_incidentBands_card_le

end LocalDirectionCycle
end DirectionData
end JSP000404Research
