import JSP000404Research.GapArc
import Mathlib.Tactic

/-!
# Linearizing a cyclic gap system at its exceptional gap

After cyclically reindexing the rays so that the unique positive-quotient gap
is the last gap, every ray coordinate can be measured by a prefix sum of the
remaining gaps.  Every such prefix avoids the exceptional gap, so the
unit-deficit remainder budget puts all coordinates into one short interval.

This is the finite ordered part of the `ell = 1 -> projective interval`
bridge.  The only remaining geometric task is to sort the actual projective
rays cyclically and identify their representatives with these prefix
coordinates.
-/

namespace JSP000404Research

open scoped BigOperators

/-- The final index of `Fin m`, for a nonempty index set. -/
def lastGapIndex (m : ℕ) (hm : 0 < m) : Fin m :=
  ⟨m - 1, by omega⟩

/-- Indices strictly preceding `j` in the chosen linearization. -/
noncomputable def prefixIndices {m : ℕ} (j : Fin m) : Finset (Fin m) := by
  classical
  exact Finset.univ.filter fun r ↦ r.val < j.val

/-- Prefix gap mass from the first ray to ray `j`. -/
noncomputable def prefixGap {m : ℕ}
    (gap : Fin m → ℝ) (j : Fin m) : ℝ :=
  ∑ r ∈ prefixIndices j, gap r

theorem lastGap_not_mem_prefix
    {m : ℕ} (hm : 0 < m) (j : Fin m) :
    lastGapIndex m hm ∉ prefixIndices j := by
  classical
  simp only [prefixIndices, Finset.mem_filter, Finset.mem_univ, true_and,
    lastGapIndex]
  omega

theorem prefixGap_nonneg
    {m : ℕ} (gap : Fin m → ℝ)
    (hgap0 : ∀ i, 0 ≤ gap i)
    (j : Fin m) :
    0 ≤ prefixGap gap j := by
  unfold prefixGap
  exact Finset.sum_nonneg fun i _ => hgap0 i

/-- If the last gap is the unique positive-quotient gap, every prefix is
bounded by the total zero-gap mass. -/
theorem prefixGap_le_zeroGapMass
    {m : ℕ} (hm : 0 < m)
    (gap : Fin m → ℝ) (q : Fin m → ℕ)
    (hgap0 : ∀ i, 0 ≤ gap i)
    (hlast : q (lastGapIndex m hm) ≠ 0)
    (hunique : ∀ j, q j ≠ 0 → j = lastGapIndex m hm)
    (j : Fin m) :
    prefixGap gap j ≤ zeroGapMass gap q := by
  unfold prefixGap
  exact sum_gap_le_zeroGapMass_of_avoids_unique
    gap q hgap0 hlast hunique (prefixIndices j)
    (lastGap_not_mem_prefix hm j)

/-- Under the unit-deficit hypotheses, every prefix has scaled length at most
`delta`. -/
theorem unit_deficit_prefix_scaled_le
    {m : ℕ} (hm : 0 < m)
    (gap : Fin m → ℝ) (q : Fin m → ℕ)
    (n : ℕ) (delta t : ℝ)
    (hn : 2 ≤ n)
    (ht : t = (n : ℝ) + delta)
    (ht0 : 0 ≤ t)
    (hgap0 : ∀ i, 0 ≤ gap i)
    (hgap : (∑ i, gap i) = 1)
    (hQle : (∑ i, q i) ≤ n)
    (hell : n - floorExcess q = 1)
    (hfloor : ∀ i, (q i : ℝ) ≤ t * gap i)
    (hlast : q (lastGapIndex m hm) ≠ 0)
    (hunique : ∀ j, q j ≠ 0 → j = lastGapIndex m hm)
    (j : Fin m) :
    t * prefixGap gap j ≤ delta := by
  unfold prefixGap
  exact unit_deficit_arc_budget
    gap q n delta t hn ht hgap0 hgap hQle hell hfloor
    hlast hunique (prefixIndices j) (lastGap_not_mem_prefix hm j) ht0

/-- With `lam = pi/t`, the actual angular prefix lies in
`[0, delta*lam]`. -/
theorem unit_deficit_prefix_angle_bounds
    {m : ℕ} (hm : 0 < m)
    (gap : Fin m → ℝ) (q : Fin m → ℕ)
    (n : ℕ) (delta t lam : ℝ)
    (hn : 2 ≤ n)
    (ht : t = (n : ℝ) + delta)
    (htpos : 0 < t)
    (hlam : lam = Real.pi / t)
    (hgap0 : ∀ i, 0 ≤ gap i)
    (hgap : (∑ i, gap i) = 1)
    (hQle : (∑ i, q i) ≤ n)
    (hell : n - floorExcess q = 1)
    (hfloor : ∀ i, (q i : ℝ) ≤ t * gap i)
    (hlast : q (lastGapIndex m hm) ≠ 0)
    (hunique : ∀ j, q j ≠ 0 → j = lastGapIndex m hm)
    (j : Fin m) :
    0 ≤ Real.pi * prefixGap gap j ∧
      Real.pi * prefixGap gap j ≤ delta * lam := by
  have hprefix0 := prefixGap_nonneg gap hgap0 j
  have hscaled :=
    unit_deficit_prefix_scaled_le
      hm gap q n delta t hn ht htpos.le hgap0 hgap hQle hell
      hfloor hlast hunique j
  constructor
  · exact mul_nonneg Real.pi_pos.le hprefix0
  · have hfactor : 0 ≤ Real.pi / t := (div_pos Real.pi_pos htpos).le
    have hmul :=
      mul_le_mul_of_nonneg_left hscaled hfactor
    calc
      Real.pi * prefixGap gap j =
          (Real.pi / t) * (t * prefixGap gap j) := by
            field_simp [htpos.ne']
      _ ≤ (Real.pi / t) * delta := hmul
      _ = delta * lam := by rw [hlam]; ring

/-- All linearized ray parameters lie in one interval of the desired sharp
width. -/
theorem unit_deficit_prefix_interval
    {m : ℕ} (hm : 0 < m)
    (gap : Fin m → ℝ) (q : Fin m → ℕ)
    (n : ℕ) (delta t lam : ℝ)
    (hn : 2 ≤ n)
    (ht : t = (n : ℝ) + delta)
    (htpos : 0 < t)
    (hlam : lam = Real.pi / t)
    (hgap0 : ∀ i, 0 ≤ gap i)
    (hgap : (∑ i, gap i) = 1)
    (hQle : (∑ i, q i) ≤ n)
    (hell : n - floorExcess q = 1)
    (hfloor : ∀ i, (q i : ℝ) ≤ t * gap i)
    (hlast : q (lastGapIndex m hm) ≠ 0)
    (hunique : ∀ j, q j ≠ 0 → j = lastGapIndex m hm) :
    ∀ j : Fin m,
      0 ≤ Real.pi * prefixGap gap j ∧
      Real.pi * prefixGap gap j ≤ delta * lam := by
  intro j
  exact unit_deficit_prefix_angle_bounds
    hm gap q n delta t lam hn ht htpos hlam hgap0 hgap hQle hell
    hfloor hlast hunique j

#print axioms lastGap_not_mem_prefix
#print axioms prefixGap_nonneg
#print axioms prefixGap_le_zeroGapMass
#print axioms unit_deficit_prefix_scaled_le
#print axioms unit_deficit_prefix_angle_bounds
#print axioms unit_deficit_prefix_interval

end JSP000404Research
