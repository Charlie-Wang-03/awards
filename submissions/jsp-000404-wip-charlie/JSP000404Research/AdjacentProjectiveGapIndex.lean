
import JSP000404Research.CentreRayIndex
import JSP000404Research.CentreQuotientData
import Mathlib.Tactic

/-!
# Consecutive sorted-angle indices produce actual projective gaps

For a nonempty angle list a::xs, the m-th entry of successiveDiffsFrom a xs
is exactly

  angle[m+1] - angle[m].

Hence every consecutive pair of indices in a CentreProjectiveCycle produces a
member of its physical gap list, of its normalized gap list, and after taking
floors, of its quotient list.
-/

namespace JSP000404Research

open Real

theorem successiveDiffsFrom_getElem_eq_adjacent_diff
    (a : ℝ) (xs : List ℝ)
    (m : ℕ)
    (hm : m < xs.length) :
    (successiveDiffsFrom a xs)[m] =
      (a :: xs)[m + 1] - (a :: xs)[m] := by
  induction xs generalizing a m with
  | nil =>
      simp at hm
  | cons b bs ih =>
      cases m with
      | zero =>
          simp [successiveDiffsFrom]
      | succ m =>
          have hm' : m < bs.length := by
            simpa using hm
          simpa [successiveDiffsFrom] using
            ih b m hm'

/-- Consecutive entries of a nonempty angle list determine a physical
projective gap member. -/
theorem adjacent_diff_mem_projectiveGaps
    (a : ℝ) (xs : List ℝ)
    (m : ℕ)
    (hm : m + 1 < (a :: xs).length) :
    (a :: xs)[m + 1] - (a :: xs)[m] ∈
      projectiveGaps (a :: xs) := by
  have hmTail : m < xs.length := by
    simpa using hm
  have hmem :
      (successiveDiffsFrom a xs)[m] ∈
        successiveDiffsFrom a xs :=
    List.getElem_mem
      (successiveDiffsFrom a xs) m
      (by simpa [successiveDiffsFrom_length] using hmTail)
  have heq :=
    successiveDiffsFrom_getElem_eq_adjacent_diff
      a xs m hmTail
  simp only [projectiveGaps, List.mem_append,
    List.mem_singleton]
  left
  rw [← heq]
  exact hmem

/-- Normalized version. -/
theorem adjacent_normalized_diff_mem_normalizedProjectiveGaps
    (a : ℝ) (xs : List ℝ)
    (m : ℕ)
    (hm : m + 1 < (a :: xs).length) :
    (((a :: xs)[m + 1] - (a :: xs)[m]) / Real.pi)
      ∈ normalizedProjectiveGaps (a :: xs) := by
  unfold normalizedProjectiveGaps
  apply List.mem_map.mpr
  exact ⟨
    (a :: xs)[m + 1] - (a :: xs)[m],
    adjacent_diff_mem_projectiveGaps a xs m hm,
    rfl⟩

/-- Quotient-list version for a consecutive angle pair. -/
theorem adjacent_quotient_mem_quotientList
    (t a : ℝ) (xs : List ℝ)
    (m : ℕ)
    (hm : m + 1 < (a :: xs).length) :
    Nat.floor
        (t * (((a :: xs)[m + 1] - (a :: xs)[m]) / Real.pi))
      ∈
    quotientList t (normalizedProjectiveGaps (a :: xs)) := by
  unfold quotientList
  apply List.mem_map.mpr
  exact ⟨
    ((a :: xs)[m + 1] - (a :: xs)[m]) / Real.pi,
    adjacent_normalized_diff_mem_normalizedProjectiveGaps
      a xs m hm,
    rfl⟩

/-- Centre-cycle specialization. -/
theorem centre_adjacent_angle_quotient_mem
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane} {hp : Function.Injective p} {i : V}
    (C : CentreProjectiveCycle hp i)
    (t : ℝ)
    (m : ℕ)
    (hm : m + 1 < C.angles.length) :
    Nat.floor
        (t * ((C.angles[m + 1] - C.angles[m]) / Real.pi))
      ∈
    quotientList t C.gaps := by
  obtain ⟨a, xs, hangles⟩ :
      ∃ a xs, C.angles = a :: xs := by
    cases h : C.angles with
    | nil =>
        exact False.elim (C.angles_nonempty h)
    | cons a xs =>
        exact ⟨a, xs, h⟩
  rw [CentreProjectiveCycle.gaps, hangles]
  have hm' : m + 1 < (a :: xs).length := by
    simpa [hangles] using hm
  simpa [hangles] using
    adjacent_quotient_mem_quotientList
      t a xs m hm'


/-- The cyclic wrap quotient of a nonempty angle list is an actual quotient-list
member. -/
theorem wrap_quotient_mem_quotientList
    (t a : ℝ) (xs : List ℝ) :
    Nat.floor
        (t * ((a + Real.pi - xs.getLastD a) / Real.pi))
      ∈
    quotientList t (normalizedProjectiveGaps (a :: xs)) := by
  unfold quotientList normalizedProjectiveGaps projectiveGaps
  simp

/-- Centre-cycle wrap specialization after displaying its angle list. -/
theorem centre_wrap_quotient_mem
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane} {hp : Function.Injective p} {i : V}
    (C : CentreProjectiveCycle hp i)
    (t a : ℝ) (xs : List ℝ)
    (hangles : C.angles = a :: xs) :
    Nat.floor
        (t * ((a + Real.pi - xs.getLastD a) / Real.pi))
      ∈
    quotientList t C.gaps := by
  rw [CentreProjectiveCycle.gaps, hangles]
  exact wrap_quotient_mem_quotientList t a xs

#print axioms successiveDiffsFrom_getElem_eq_adjacent_diff
#print axioms adjacent_diff_mem_projectiveGaps
#print axioms centre_adjacent_angle_quotient_mem
#print axioms wrap_quotient_mem_quotientList
#print axioms centre_wrap_quotient_mem

end JSP000404Research
