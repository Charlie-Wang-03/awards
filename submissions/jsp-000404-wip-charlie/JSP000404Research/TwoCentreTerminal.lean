import JSP000404Research.ZeroCarry
import JSP000404Research.CentreQuotientData
import Mathlib.Tactic

/-!
# Two-centre terminal arithmetic at a fixed Sendov parameter

Let

  t = n + delta,   1 <= n,   0 <= delta < 1.

Then floor(t)=n.

A centre with exactly one normalized projective gap has gap list [1], hence
quotient list [n].  Its floor-excess exponent is n-1.  Therefore a two-centre
terminal contributes

  2 * 2^(n-1) = 2^n.

This is the direct terminal capacity needed by AggregateSplitTree.  No child
exact-normalization theorem is invoked.
-/

namespace JSP000404Research

theorem natFloor_sendov_scale
    {n : ℕ} {delta t : ℝ}
    (hn : 1 ≤ n)
    (hdelta0 : 0 ≤ delta)
    (hdelta1 : delta < 1)
    (ht : t = (n : ℝ) + delta) :
    Nat.floor t = n := by
  have ht0 : 0 ≤ t := by
    rw [ht]
    have hn0 : (0 : ℝ) ≤ n := by positivity
    linarith
  apply (Nat.floor_eq_iff ht0).2
  constructor
  · rw [ht]
    exact_mod_cast (Nat.le_add_right n 0)
  · rw [ht]
    push_cast
    linarith

theorem quotientList_singleton_one
    {n : ℕ} {delta t : ℝ}
    (hn : 1 ≤ n)
    (hdelta0 : 0 ≤ delta)
    (hdelta1 : delta < 1)
    (ht : t = (n : ℝ) + delta) :
    quotientList t [1] = [n] := by
  have hf :=
    natFloor_sendov_scale hn hdelta0 hdelta1 ht
  simp [quotientList, hf]

theorem floorExcess_fin_one_const
    (q : ℕ) :
    floorExcess (fun _ : Fin 1 => q) = q - 1 := by
  simp [floorExcess]

theorem two_centre_exponent_eq
    {n : ℕ} {delta t : ℝ}
    (hn : 1 ≤ n)
    (hdelta0 : 0 ≤ delta)
    (hdelta1 : delta < 1)
    (ht : t = (n : ℝ) + delta) :
    floorExcess (fun _ : Fin 1 => Nat.floor t) = n - 1 := by
  rw [floorExcess_fin_one_const,
      natFloor_sendov_scale hn hdelta0 hdelta1 ht]

/-- Exact dyadic mass of the two-centre fixed-t terminal. -/
theorem two_centre_terminal_weight
    {n : ℕ}
    (hn : 1 ≤ n) :
    2 * 2 ^ (n - 1) = 2 ^ n := by
  have hsucc : n - 1 + 1 = n := by omega
  calc
    2 * 2 ^ (n - 1)
        = 2 ^ (n - 1) * 2 := by ring
    _ = 2 ^ ((n - 1) + 1) := by
      rw [pow_succ]
    _ = 2 ^ n := by rw [hsucc]

/-- Combined terminal statement in exponent form. -/
theorem two_centre_fixed_t_capacity
    {n : ℕ} {delta t : ℝ}
    (hn : 1 ≤ n)
    (hdelta0 : 0 ≤ delta)
    (hdelta1 : delta < 1)
    (ht : t = (n : ℝ) + delta) :
    2 *
      2 ^ floorExcess (fun _ : Fin 1 => Nat.floor t)
      = 2 ^ n := by
  rw [two_centre_exponent_eq hn hdelta0 hdelta1 ht]
  exact two_centre_terminal_weight hn

#print axioms natFloor_sendov_scale
#print axioms quotientList_singleton_one
#print axioms two_centre_exponent_eq
#print axioms two_centre_terminal_weight
#print axioms two_centre_fixed_t_capacity

end JSP000404Research
