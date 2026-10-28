import JSP000404Research.PlanarThreeExactResidualCapacity
import JSP000404Research.CentreExponentBounds
import Mathlib.Tactic

/-!
# Exact exhaustive original n=3 remaining profile

For actual n=3 AngleCap projective cycles and 0 <= delta < 1/2,
each exponent k_i lies in {0,1,2}. Rather than assuming that
low-support surplus can be paid by unavailable Boolean credits,
we count the true original exponent-one and exponent-two centres.

The global original n=3 dyadic capacity is EXACTLY equivalent to:
 * N = 7: no exponent-two centre and at most one exponent-one;
 * N = 8: all exponents zero;
 * N >= 9: impossible for the capacity bound;
when N >= 7 is already known.

These are mathematical necessary-and-sufficient numerical profiles.
The planar exclusion of their complementary geometric motifs is
NOT proved and no extra axiom or admitted theorem is introduced.
-/

namespace JSP000404Research
open scoped BigOperators

/-- Exact arithmetic census for any finite k taking values in {0,1,2}.
Unlike a coarse cardinality bound, this exposes all integer debt. -/
theorem three_level_dyadic_sum_exact
    {V : Type*} [Fintype V] (k : V → ℕ)
    (hk : ∀ i, k i ≤ 2) :
    (∑ i : V, (2 : ℕ) ^ k i) =
      Fintype.card V +
      ((Finset.univ : Finset V).filter (fun i => k i = 1)).card +
      3 * ((Finset.univ : Finset V).filter (fun i => k i = 2)).card := by
  classical
  have hp (i : V) :
      (2 : ℕ) ^ k i =
        1 + (if k i = 1 then 1 else 0) +
          (if k i = 2 then 3 else 0) := by
    have hi := hk i
    interval_cases h : k i <;> simp [h]
  calc
    (∑ i : V, (2 : ℕ) ^ k i) =
      ∑ i : V, (1 + (if k i = 1 then 1 else 0) +
        (if k i = 2 then 3 else 0)) := by
        apply Finset.sum_congr rfl
        intro i _
        exact hp i
    _ = Fintype.card V +
        ((Finset.univ : Finset V).filter (fun i => k i = 1)).card +
        3 * ((Finset.univ : Finset V).filter (fun i => k i = 2)).card := by
        simp [Finset.sum_add_distrib, Finset.sum_ite, mul_comm]

/-- Original planar n=3 geometry has an EXACT top/next integer
ledger, with no synthetic hole or surplus credit. -/
theorem planar_three_original_top_next_exact_ledger
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane}
    (hp : Function.Injective p)
    {t delta : ℝ}
    (hdelta0 : 0 ≤ delta)
    (hdeltaHalf : delta < (1 : ℝ) / 2)
    (ht : t = (3 : ℝ) + delta)
    (C : ∀ i : V, CentreProjectiveCycle hp i) :
    (∑ i : V, 2 ^ centreExponent (C i) t) =
      Fintype.card V +
      ((Finset.univ : Finset V).filter
        (fun i => centreExponent (C i) t = 1)).card +
      3 * ((Finset.univ : Finset V).filter
        (fun i => centreExponent (C i) t = 2)).card := by
  have hdelta1 : delta < 1 := by linarith
  have hk : ∀ i : V, centreExponent (C i) t ≤ 2 := by
    intro i
    have hh := centreExponent_lt_n (C i) 3 delta t
      (by decide : 1 ≤ (3 : ℕ)) hdelta0 hdelta1 ht
    omega
  exact three_level_dyadic_sum_exact
    (fun i => centreExponent (C i) t) hk

/-- For a genuine original configuration with N>=7, this is the
EXACT if-and-only-if finite arithmetic target for the original
8-unit dyadic bound. The remaining task is planar exclusion of
N>=9 and of the stated top/next overweight motifs at N=7,8. -/
theorem planar_three_large_capacity_iff_exact_profile
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane}
    (hp : Function.Injective p)
    {t delta : ℝ}
    (hdelta0 : 0 ≤ delta)
    (hdeltaHalf : delta < (1 : ℝ) / 2)
    (ht : t = (3 : ℝ) + delta)
    (C : ∀ i : V, CentreProjectiveCycle hp i)
    (hseven : 7 ≤ Fintype.card V) :
    ((∑ i : V, 2 ^ centreExponent (C i) t) ≤ 8) ↔
      ((Fintype.card V = 7 ∧
          ((Finset.univ : Finset V).filter
            (fun i => centreExponent (C i) t = 2)).card = 0 ∧
          ((Finset.univ : Finset V).filter
            (fun i => centreExponent (C i) t = 1)).card ≤ 1) ∨
       (Fintype.card V = 8 ∧
          ((Finset.univ : Finset V).filter
            (fun i => centreExponent (C i) t = 2)).card = 0 ∧
          ((Finset.univ : Finset V).filter
            (fun i => centreExponent (C i) t = 1)).card = 0)) := by
  rw [planar_three_original_top_next_exact_ledger hp hdelta0 hdeltaHalf ht C]
  omega

/-- As a strictly equivalent *necessary* configuration census, an
overweight n=3 original set with at least seven centres must either
have >=9 actual centres, or N=8 with a positive k=1 or k=2 count,
or N=7 with two k=1 centres or one k=2 centre. -/
theorem planar_three_large_overweight_iff_obstruction_profile
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane}
    (hp : Function.Injective p)
    {t delta : ℝ}
    (hdelta0 : 0 ≤ delta)
    (hdeltaHalf : delta < (1 : ℝ) / 2)
    (ht : t = (3 : ℝ) + delta)
    (C : ∀ i : V, CentreProjectiveCycle hp i)
    (hseven : 7 ≤ Fintype.card V) :
    (8 < (∑ i : V, 2 ^ centreExponent (C i) t)) ↔
      (9 ≤ Fintype.card V ∨
       (Fintype.card V = 8 ∧
          (0 < ((Finset.univ : Finset V).filter
            (fun i => centreExponent (C i) t = 1)).card ∨
           0 < ((Finset.univ : Finset V).filter
            (fun i => centreExponent (C i) t = 2)).card)) ∨
       (Fintype.card V = 7 ∧
          (2 ≤ ((Finset.univ : Finset V).filter
            (fun i => centreExponent (C i) t = 1)).card ∨
           1 ≤ ((Finset.univ : Finset V).filter
            (fun i => centreExponent (C i) t = 2)).card))) := by
  rw [planar_three_original_top_next_exact_ledger hp hdelta0 hdeltaHalf ht C]
  omega

#print axioms three_level_dyadic_sum_exact
#print axioms planar_three_original_top_next_exact_ledger
#print axioms planar_three_large_capacity_iff_exact_profile
#print axioms planar_three_large_overweight_iff_obstruction_profile

end JSP000404Research
