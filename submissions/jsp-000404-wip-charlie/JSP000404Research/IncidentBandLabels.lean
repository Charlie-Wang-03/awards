import JSP000404Research.OrderedBandCode
import JSP000404Research.FiniteProjectiveRays
import Mathlib.Data.Finset.Card
import Mathlib.Tactic

/-!
# Incident unit bands are the distinct floors of unordered incident values

For ordered direction data D and a fixed centre v, orient every incident edge
by the ambient vertex order and record its nonnegative direction value.

The unit-band label of a neighbour is simply the natural floor of this value.
For any complete list of all neighbours:

  distinct floor labels = incidentBands D k v.

This is the abstract bridge needed to turn the used-band term in the cyclic
band-jump inequality into the actual local palette size of OrderedBandCode.
-/

namespace JSP000404Research
namespace DirectionData

noncomputable def incidentValueAt
    {V : Type*} [LinearOrder V]
    {width : ℝ}
    (D : DirectionData V width)
    (v : V)
    (j : OtherVertex v) : ℝ :=
  if h : j.1 < v then
    D.value j.1 v
  else
    D.value v j.1

theorem incidentValueAt_nonneg
    {V : Type*} [LinearOrder V]
    {width : ℝ}
    (D : DirectionData V width)
    (v : V)
    (j : OtherVertex v) :
    0 ≤ incidentValueAt D v j := by
  by_cases h : j.1 < v
  · simp [incidentValueAt, h, D.nonnegative h]
  · have hvj : v < j.1 :=
      lt_of_le_of_ne (not_lt.mp h) j.2.symm
    simp [incidentValueAt, h, D.nonnegative hvj]

theorem incidentValueAt_lt_width
    {V : Type*} [LinearOrder V]
    {width : ℝ}
    (D : DirectionData V width)
    (v : V)
    (j : OtherVertex v) :
    incidentValueAt D v j < width := by
  by_cases h : j.1 < v
  · simp [incidentValueAt, h, D.belowWidth h]
  · have hvj : v < j.1 :=
      lt_of_le_of_ne (not_lt.mp h) j.2.symm
    simp [incidentValueAt, h, D.belowWidth hvj]

noncomputable def incidentBandAt
    {V : Type*} [LinearOrder V]
    {width : ℝ}
    (D : DirectionData V width)
    (k : ℕ)
    (hwidth : width ≤ (k : ℝ))
    (v : V)
    (j : OtherVertex v) : Fin k :=
  ⟨Nat.floor (incidentValueAt D v j), by
    have hx0 := incidentValueAt_nonneg D v j
    have hxk :
        incidentValueAt D v j < (k : ℝ) :=
      (incidentValueAt_lt_width D v j).trans_le hwidth
    exact (Nat.floor_lt hx0).2 hxk⟩

@[simp] theorem incidentBandAt_val
    {V : Type*} [LinearOrder V]
    {width : ℝ}
    (D : DirectionData V width)
    (k : ℕ)
    (hwidth : width ≤ (k : ℝ))
    (v : V)
    (j : OtherVertex v) :
    (incidentBandAt D k hwidth v j).val =
      Nat.floor (incidentValueAt D v j) := rfl

/-- A retained band is incident iff it is the floor label of some neighbour. -/
theorem mem_incidentBands_iff_exists_incidentBandAt
    {V : Type*} [LinearOrder V]
    {width : ℝ}
    (D : DirectionData V width)
    (k : ℕ)
    (hwidth : width ≤ (k : ℝ))
    (v : V)
    (m : Fin k) :
    m ∈ incidentBands D k v ↔
      ∃ j : OtherVertex v,
        incidentBandAt D k hwidth v j = m := by
  classical
  simp only [incidentBands, Finset.mem_filter,
    Finset.mem_univ, true_and]
  constructor
  · intro hm
    rcases hm with
        ⟨w, hwv, hmlo, hmhi⟩ |
        ⟨w, hvw, hmlo, hmhi⟩
    · let j : OtherVertex v := ⟨w, ne_of_lt hwv⟩
      refine ⟨j, ?_⟩
      apply Fin.ext
      have hfloor :
          Nat.floor (D.value w v) = m.val :=
        (Nat.floor_eq_iff (D.nonnegative hwv)).2
          (by simpa using And.intro hmlo hmhi)
      simpa [incidentBandAt, incidentValueAt, j, hwv]
        using hfloor
    · let j : OtherVertex v := ⟨w, ne_of_gt hvw⟩
      refine ⟨j, ?_⟩
      apply Fin.ext
      have hfloor :
          Nat.floor (D.value v w) = m.val :=
        (Nat.floor_eq_iff (D.nonnegative hvw)).2
          (by simpa using And.intro hmlo hmhi)
      have hnot : ¬ w < v := not_lt_of_ge hvw.le
      simpa [incidentBandAt, incidentValueAt, j, hnot]
        using hfloor
  · rintro ⟨j, hj⟩
    by_cases h : j.1 < v
    · left
      refine ⟨j.1, h, ?_, ?_⟩
      have hx0 := D.nonnegative h
      have hlo :
          ((Nat.floor (D.value j.1 v) : ℕ) : ℝ) ≤
            D.value j.1 v :=
        Nat.floor_le hx0
      have hhi :
          D.value j.1 v <
            ((Nat.floor (D.value j.1 v) : ℕ) : ℝ) + 1 :=
        Nat.lt_floor_add_one _
      have hfloor :
          Nat.floor (D.value j.1 v) = m.val := by
        have hval := congrArg Fin.val hj
        simpa [incidentBandAt, incidentValueAt, h] using hval
      rw [hfloor] at hlo hhi
      · simpa using hlo
      · simpa using hhi
    · have hvj : v < j.1 :=
        lt_of_le_of_ne (not_lt.mp h) j.2.symm
      right
      refine ⟨j.1, hvj, ?_, ?_⟩
      have hx0 := D.nonnegative hvj
      have hlo :
          ((Nat.floor (D.value v j.1) : ℕ) : ℝ) ≤
            D.value v j.1 :=
        Nat.floor_le hx0
      have hhi :
          D.value v j.1 <
            ((Nat.floor (D.value v j.1) : ℕ) : ℝ) + 1 :=
        Nat.lt_floor_add_one _
      have hfloor :
          Nat.floor (D.value v j.1) = m.val := by
        have hval := congrArg Fin.val hj
        simpa [incidentBandAt, incidentValueAt, h] using hval
      rw [hfloor] at hlo hhi
      · simpa using hlo
      · simpa using hhi

/-- A complete neighbour list has exactly the incident finite band labels. -/
theorem incidentBandAt_toFinset_eq_incidentBands
    {V : Type*} [LinearOrder V] [Fintype V]
    {width : ℝ}
    (D : DirectionData V width)
    (k : ℕ)
    (hwidth : width ≤ (k : ℝ))
    (v : V)
    (rays : List (OtherVertex v))
    (hcomplete : rays.toFinset = Finset.univ) :
    (rays.map (incidentBandAt D k hwidth v)).toFinset =
      incidentBands D k v := by
  classical
  ext m
  constructor
  · intro hm
    rw [List.mem_toFinset, List.mem_map] at hm
    obtain ⟨j, hj, rfl⟩ := hm
    exact (mem_incidentBands_iff_exists_incidentBandAt
      D k hwidth v _).2 ⟨j, rfl⟩
  · intro hm
    obtain ⟨j, hj⟩ :=
      (mem_incidentBands_iff_exists_incidentBandAt
        D k hwidth v m).1 hm
    rw [List.mem_toFinset, List.mem_map]
    refine ⟨j, ?_, hj⟩
    have hjFin : j ∈ rays.toFinset := by
      rw [hcomplete]
      simp
    simpa using hjFin

/-- Cardinal form using natural floor labels rather than Fin k labels. -/
theorem incidentFloorLabels_card_eq_incidentBands_card
    {V : Type*} [LinearOrder V] [Fintype V]
    {width : ℝ}
    (D : DirectionData V width)
    (k : ℕ)
    (hwidth : width ≤ (k : ℝ))
    (v : V)
    (rays : List (OtherVertex v))
    (hcomplete : rays.toFinset = Finset.univ) :
    ((rays.map (incidentValueAt D v)).map Nat.floor).toFinset.card =
      (incidentBands D k v).card := by
  classical
  have hset :
      ((rays.map (incidentValueAt D v)).map Nat.floor).toFinset =
        (incidentBands D k v).image Fin.val := by
    rw [← incidentBandAt_toFinset_eq_incidentBands
      D k hwidth v rays hcomplete]
    ext q
    simp [incidentBandAt, Function.comp_def]
  rw [hset]
  exact Finset.card_image_of_injective
    _ Fin.val_injective

#print axioms incidentValueAt_nonneg
#print axioms mem_incidentBands_iff_exists_incidentBandAt
#print axioms incidentBandAt_toFinset_eq_incidentBands
#print axioms incidentFloorLabels_card_eq_incidentBands_card

end DirectionData
end JSP000404Research
