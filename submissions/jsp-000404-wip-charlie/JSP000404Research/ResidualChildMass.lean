
import JSP000404Research.ResidualChildColoring
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic

/-!
# True subtype masses of the two residual children

ResidualBinaryRecursion first wrote the child masses as indicator sums over the
ambient vertex type.  ResidualChildColoring then constructed the actual subtype
children

  LeftResidualChild  = {v | not HighSink(v)},
  RightResidualChild = {v | not HighSource(v)}.

This file identifies the two descriptions exactly.

Hence the root mass is bounded by the genuine subtype child masses

  sum_v 2^k(v)
    <=
  sum_{v in LeftChild}  2^kL(v)
    +
  sum_{v in RightChild} 2^kR(v).

Any recursive capacity theorem on the actual child types can therefore be
plugged in directly.
-/

namespace JSP000404Research
namespace DirectionData

open scoped BigOperators

/-- The residual predicate is geometric and generally noncomputable.
Materialize its finite subtype classically so the mass statements elaborate
without synthetic sorry-based placeholder instances. -/
noncomputable instance leftResidualChildFintype
    {V : Type*} [LinearOrder V] [Fintype V] {width : ℝ}
    (D : DirectionData V width) (n : ℕ) :
    Fintype (LeftResidualChild D n) := by
  classical
  dsimp [LeftResidualChild]
  infer_instance

noncomputable instance rightResidualChildFintype
    {V : Type*} [LinearOrder V] [Fintype V] {width : ℝ}
    (D : DirectionData V width) (n : ℕ) :
    Fintype (RightResidualChild D n) := by
  classical
  dsimp [RightResidualChild]
  infer_instance

theorem leftChildWeight_sum_eq_subtype_mass
    {V : Type*} [LinearOrder V] [Fintype V]
    {width : ℝ} {n : ℕ}
    (D : DirectionData V width)
    (exponent : V → ℕ) :
    (∑ v, leftChildWeight D n exponent v) =
      ∑ v : LeftResidualChild D n,
        2 ^ leftChildExponent D n exponent v.1 := by
  classical
  have h :=
    Fintype.sum_subtype_add_sum_subtype
      (fun v : V => HighSink D n v)
      (fun v => leftChildWeight D n exponent v)
  have hzero :
      (∑ v : {x : V // HighSink D n x},
        leftChildWeight D n exponent v.1) = 0 := by
    apply Finset.sum_eq_zero
    intro v _
    simp [leftChildWeight, v.2]
  rw [hzero, zero_add] at h
  refine h.symm.trans ?_
  apply Finset.sum_congr rfl
  intro v _
  simp [leftChildWeight, v.2]

theorem rightChildWeight_sum_eq_subtype_mass
    {V : Type*} [LinearOrder V] [Fintype V]
    {width : ℝ} {n : ℕ}
    (D : DirectionData V width)
    (exponent : V → ℕ) :
    (∑ v, rightChildWeight D n exponent v) =
      ∑ v : RightResidualChild D n,
        2 ^ rightChildExponent D n exponent v.1 := by
  classical
  have h :=
    Fintype.sum_subtype_add_sum_subtype
      (fun v : V => HighSource D n v)
      (fun v => rightChildWeight D n exponent v)
  have hzero :
      (∑ v : {x : V // HighSource D n x},
        rightChildWeight D n exponent v.1) = 0 := by
    apply Finset.sum_eq_zero
    intro v _
    simp [rightChildWeight, v.2]
  rw [hzero, zero_add] at h
  refine h.symm.trans ?_
  apply Finset.sum_congr rfl
  intro v _
  simp [rightChildWeight, v.2]

/-- Root mass is bounded by the genuine two child subtype masses. -/
theorem root_mass_le_child_subtype_masses
    {V : Type*} [LinearOrder V] [Fintype V]
    {width delta : ℝ} {n : ℕ}
    (D : DirectionData V width)
    (hwidth : width = (n : ℝ) + delta)
    (hdelta : delta < 1)
    (exponent : V → ℕ) :
    (∑ v, 2 ^ exponent v) ≤
      (∑ v : LeftResidualChild D n,
        2 ^ leftChildExponent D n exponent v.1) +
      (∑ v : RightResidualChild D n,
        2 ^ rightChildExponent D n exponent v.1) := by
  have hroot :=
    root_mass_le_residual_children
      D hwidth hdelta exponent
  rw [leftChildWeight_sum_eq_subtype_mass,
      rightChildWeight_sum_eq_subtype_mass] at hroot
  exact hroot

/-- Recursive closure in the form actually needed later: half-capacity on each
actual child subtype gives the sharp parent capacity. -/
theorem root_capacity_of_child_subtype_capacities
    {V : Type*} [LinearOrder V] [Fintype V]
    {width delta : ℝ} {n : ℕ}
    (D : DirectionData V width)
    (hwidth : width = (n : ℝ) + delta)
    (hdelta : delta < 1)
    (exponent : V → ℕ)
    (hn : 1 ≤ n)
    (hleft :
      (∑ v : LeftResidualChild D n,
        2 ^ leftChildExponent D n exponent v.1)
        ≤ 2 ^ (n - 1))
    (hright :
      (∑ v : RightResidualChild D n,
        2 ^ rightChildExponent D n exponent v.1)
        ≤ 2 ^ (n - 1)) :
    (∑ v, 2 ^ exponent v) ≤ 2 ^ n := by
  have hroot :=
    root_mass_le_child_subtype_masses
      D hwidth hdelta exponent
  have hpow :
      2 ^ n = 2 * 2 ^ (n - 1) := by
    cases n with
    | zero => omega
    | succ m =>
        simp [pow_succ, mul_comm]
  rw [hpow]
  omega

#print axioms leftChildWeight_sum_eq_subtype_mass
#print axioms rightChildWeight_sum_eq_subtype_mass
#print axioms root_mass_le_child_subtype_masses
#print axioms root_capacity_of_child_subtype_capacities

end DirectionData
end JSP000404Research
