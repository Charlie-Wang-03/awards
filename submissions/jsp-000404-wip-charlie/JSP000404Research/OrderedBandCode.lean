import JSP000404Research.OrderedDirections
import JSP000404Research.WeightedDefect
import Mathlib.Data.Rat.Floor
import Mathlib.Tactic

/-!
# Unit-band partial code for ordered directions

Given ordered direction data of width at most an integer `k`, put each edge
into its half-open unit band `[m,m+1)`.

At a vertex, the Boolean bit for band `m` records whether there is an incoming
edge in that band; a coordinate is specified exactly when some incident edge
uses the band.  The middle-separation axiom implies that, for an edge `i<j`
lying in band `m`, vertex `i` cannot have an incoming edge in the same band,
while `j` does.  Thus the two endpoint partial words disagree on a commonly
specified coordinate.

This gives the weighted Hansel inequality directly from `DirectionData`.
-/

namespace JSP000404Research
namespace DirectionData

open scoped BigOperators

private def incomingBand {V : Type*} [LinearOrder V]
    {width : ℝ} (D : DirectionData V width) (m : ℕ) (v : V) : Prop :=
  ∃ w, w < v ∧ (m : ℝ) ≤ D.value w v ∧ D.value w v < (m : ℝ) + 1

/-- Unit bands incident to a vertex. -/
noncomputable def incidentBands {V : Type*} [LinearOrder V]
    {width : ℝ} (D : DirectionData V width) (k : ℕ) (v : V) :
    Finset (Fin k) := by
  classical
  exact Finset.univ.filter fun m ↦
    (∃ w, w < v ∧ (m : ℝ) ≤ D.value w v ∧ D.value w v < (m : ℝ) + 1) ∨
    (∃ w, v < w ∧ (m : ℝ) ≤ D.value v w ∧ D.value v w < (m : ℝ) + 1)

/-- Canonical incoming/outgoing bit attached to a unit band. -/
noncomputable def bandBit {V : Type*} [LinearOrder V]
    {width : ℝ} (D : DirectionData V width) (k : ℕ) :
    V → Fin k → Bool :=
  fun v m ↦ decide (incomingBand D m v)

private theorem floor_band
    {x : ℝ} {k : ℕ} (hx0 : 0 ≤ x) (hxk : x < k) :
    ∃ m : Fin k, (m : ℝ) ≤ x ∧ x < (m : ℝ) + 1 := by
  have hm : Nat.floor x < k := (Nat.floor_lt hx0).2 hxk
  refine ⟨⟨Nat.floor x, hm⟩, ?_, ?_⟩
  · simpa using Nat.floor_le hx0
  · simpa using Nat.lt_floor_add_one x

/-- Every ordered edge supplies a coordinate specified at both endpoints and
with opposite canonical bits. -/
theorem unitBand_separates
    {V : Type*} [LinearOrder V] [Fintype V]
    {width : ℝ} (D : DirectionData V width) (k : ℕ)
    (hwidth : width ≤ k) :
    ∀ v w, v ≠ w → ∃ m,
      m ∈ incidentBands D k v ∧
      m ∈ incidentBands D k w ∧
      bandBit D k v m ≠ bandBit D k w m := by
  classical
  intro v w hvw
  wlog hvwlt : v < w generalizing v w
  · have hwv : w < v := lt_of_le_of_ne (not_lt.mp hvwlt) hvw.symm
    obtain ⟨m, hmw, hmv, hbit⟩ := this w v hvw.symm hwv
    exact ⟨m, hmv, hmw, hbit.symm⟩
  have hx0 : 0 ≤ D.value v w := D.nonnegative hvwlt
  have hxk : D.value v w < (k : ℝ) :=
    (D.belowWidth hvwlt).trans_le hwidth
  obtain ⟨m, hmlo, hmhi⟩ := floor_band hx0 hxk

  have hm_v : m ∈ incidentBands D k v := by
    simp only [incidentBands, Finset.mem_filter, Finset.mem_univ, true_and]
    exact Or.inr ⟨w, hvwlt, hmlo, hmhi⟩
  have hm_w : m ∈ incidentBands D k w := by
    simp only [incidentBands, Finset.mem_filter, Finset.mem_univ, true_and]
    exact Or.inl ⟨v, hvwlt, hmlo, hmhi⟩

  have hin_w : incomingBand D m w := ⟨v, hvwlt, hmlo, hmhi⟩
  have hnotin_v : ¬ incomingBand D m v := by
    rintro ⟨a, hav, halo, hahi⟩
    have hlarge := D.middleSeparated hav hvwlt
    have hsmall : |D.value a v - D.value v w| < 1 := by
      rw [abs_lt]
      constructor <;> linarith
    exact (not_lt_of_ge hlarge) hsmall

  refine ⟨m, hm_v, hm_w, ?_⟩
  simp [bandBit, hnotin_v, hin_w]

/-- The canonical unit-band code satisfies the weighted Hansel capacity bound. -/
theorem unitBand_weighted_capacity
    {V : Type*} [LinearOrder V] [Fintype V]
    {width : ℝ} (D : DirectionData V width) (k : ℕ)
    (hwidth : width ≤ k) :
    ∑ v, 2 ^ (k - (incidentBands D k v).card) ≤ 2 ^ k := by
  exact weighted_hansel (bandBit D k) (incidentBands D k)
    (unitBand_separates D k hwidth)

/-- Exact defect form for the canonical unit-band code. -/
theorem unitBand_defect
    {V : Type*} [LinearOrder V] [Fintype V]
    {width : ℝ} (D : DirectionData V width) (k : ℕ)
    (hwidth : width ≤ k) :
    ∑ v, (2 ^ (k - (incidentBands D k v).card) - 1) ≤
      2 ^ k - Fintype.card V := by
  exact weighted_hansel_defect (bandBit D k) (incidentBands D k)
    (unitBand_separates D k hwidth)

/-- A single vertex missing one unit band yields the strict cardinality
improvement familiar from the dyadic endpoint proof. -/
theorem unitBand_one_missing
    {V : Type*} [LinearOrder V] [Fintype V]
    {width : ℝ} (D : DirectionData V width) (k : ℕ)
    (hwidth : width ≤ k)
    (v : V) (hmissing : incidentBands D k v ≠ Finset.univ) :
    Fintype.card V + 1 ≤ 2 ^ k := by
  exact weighted_hansel_one_missing (bandBit D k) (incidentBands D k)
    (unitBand_separates D k hwidth) v hmissing

#print axioms unitBand_separates
#print axioms unitBand_weighted_capacity
#print axioms unitBand_defect
#print axioms unitBand_one_missing

end DirectionData
end JSP000404Research
