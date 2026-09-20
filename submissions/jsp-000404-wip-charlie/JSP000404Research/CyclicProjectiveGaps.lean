import JSP000404Research.SortedProjectiveRays
import Mathlib.Tactic

/-!
# Cyclic gaps of a sorted projective-angle list

For a nonempty sorted list

  a = theta_0 <= theta_1 <= ... <= theta_{m-1} < pi,

record the successive differences and finally the wrap gap

  theta_0 + pi - theta_{m-1}.

The gaps are nonnegative, there are exactly m of them, and their total is pi.
After division by pi they form a normalized gap list of total mass one.

This is the concrete gap object needed to connect canonical projective rays to
the Sendov quotient arithmetic.
-/

namespace JSP000404Research

open Real

/-- Successive forward differences, starting from an explicit previous value. -/
def successiveDiffsFrom (a : ℝ) : List ℝ → List ℝ
  | [] => []
  | b :: bs => (b - a) :: successiveDiffsFrom b bs

theorem successiveDiffsFrom_length
    (a : ℝ) (xs : List ℝ) :
    (successiveDiffsFrom a xs).length = xs.length := by
  induction xs generalizing a with
  | nil => rfl
  | cons b bs ih =>
      simp [successiveDiffsFrom, ih]

/-- Telescoping sum of successive differences. -/
theorem successiveDiffsFrom_sum
    (a : ℝ) (xs : List ℝ) :
    (successiveDiffsFrom a xs).sum =
      xs.getLastD a - a := by
  induction xs generalizing a with
  | nil =>
      simp [successiveDiffsFrom]
  | cons b bs ih =>
      simp only [successiveDiffsFrom, List.sum_cons, ih]
      rw [List.getLastD_cons]
      ring

/-- Sorted input gives nonnegative successive differences. -/
theorem successiveDiffsFrom_nonneg
    (a : ℝ) (xs : List ℝ)
    (hsorted : (a :: xs).Pairwise (· ≤ ·)) :
    ∀ d ∈ successiveDiffsFrom a xs, 0 ≤ d := by
  induction xs generalizing a with
  | nil =>
      simp [successiveDiffsFrom]
  | cons b bs ih =>
      have hab : a ≤ b := by
        exact hsorted.rel_get_of_mem (by simp)
      have htail : (b :: bs).Pairwise (· ≤ ·) :=
        hsorted.tail
      intro d hd
      simp only [successiveDiffsFrom, List.mem_cons] at hd
      rcases hd with rfl | hd
      · linarith
      · exact ih b htail d hd

/-- Physical projective cyclic gaps of a nonempty angle list. -/
def projectiveGaps : List ℝ → List ℝ
  | [] => []
  | a :: xs =>
      successiveDiffsFrom a xs ++
        [a + Real.pi - xs.getLastD a]

theorem projectiveGaps_length
    (angles : List ℝ) :
    (projectiveGaps angles).length = angles.length := by
  cases angles with
  | nil => rfl
  | cons a xs =>
      simp [projectiveGaps, successiveDiffsFrom_length]

/-- The cyclic physical gaps telescope to exactly pi. -/
theorem projectiveGaps_sum
    {a : ℝ} {xs : List ℝ} :
    (projectiveGaps (a :: xs)).sum = Real.pi := by
  simp [projectiveGaps, successiveDiffsFrom_sum]
  ring

/-- The last angle of a nonempty sorted ray list still lies below pi. -/
theorem getLastD_lt_pi_of_all_lt
    (a : ℝ) (xs : List ℝ)
    (hall : ∀ theta ∈ a :: xs, theta < Real.pi) :
    xs.getLastD a < Real.pi := by
  exact hall _ (List.getLastD_mem_cons a xs)

/-- Sorted canonical angles in [0,pi) give nonnegative cyclic gaps. -/
theorem projectiveGaps_nonneg
    (a : ℝ) (xs : List ℝ)
    (ha0 : 0 ≤ a)
    (hsorted : (a :: xs).Pairwise (· ≤ ·))
    (hall : ∀ theta ∈ a :: xs, theta < Real.pi) :
    ∀ g ∈ projectiveGaps (a :: xs), 0 ≤ g := by
  intro g hg
  simp only [projectiveGaps, List.mem_append, List.mem_singleton] at hg
  rcases hg with hdiff | rfl
  · exact successiveDiffsFrom_nonneg a xs hsorted g hdiff
  · have hlast := getLastD_lt_pi_of_all_lt a xs hall
    linarith

/-- Division by a common scalar commutes with finite list summation. -/
theorem list_sum_map_div
    (xs : List ℝ) (c : ℝ) :
    (xs.map (fun x => x / c)).sum = xs.sum / c := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
      simp [ih, add_div]

/-- Normalized projective gaps; a nonempty cycle has total mass one. -/
def normalizedProjectiveGaps (angles : List ℝ) : List ℝ :=
  (projectiveGaps angles).map (fun g => g / Real.pi)

theorem normalizedProjectiveGaps_length
    (angles : List ℝ) :
    (normalizedProjectiveGaps angles).length = angles.length := by
  simp [normalizedProjectiveGaps, projectiveGaps_length]

theorem normalizedProjectiveGaps_sum
    {a : ℝ} {xs : List ℝ} :
    (normalizedProjectiveGaps (a :: xs)).sum = 1 := by
  rw [normalizedProjectiveGaps, list_sum_map_div,
    projectiveGaps_sum]
  exact div_self Real.pi_ne_zero

theorem normalizedProjectiveGaps_nonneg
    (a : ℝ) (xs : List ℝ)
    (ha0 : 0 ≤ a)
    (hsorted : (a :: xs).Pairwise (· ≤ ·))
    (hall : ∀ theta ∈ a :: xs, theta < Real.pi) :
    ∀ g ∈ normalizedProjectiveGaps (a :: xs), 0 ≤ g := by
  intro g hg
  simp only [normalizedProjectiveGaps, List.mem_map] at hg
  obtain ⟨x, hx, rfl⟩ := hg
  exact div_nonneg
    (projectiveGaps_nonneg a xs ha0 hsorted hall x hx)
    Real.pi_pos.le

#print axioms successiveDiffsFrom_sum
#print axioms projectiveGaps_sum
#print axioms projectiveGaps_nonneg
#print axioms normalizedProjectiveGaps_sum
#print axioms normalizedProjectiveGaps_nonneg

end JSP000404Research
