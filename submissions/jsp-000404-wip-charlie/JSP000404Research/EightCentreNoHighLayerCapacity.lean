import JSP000404Research.CentreExponentBounds
import Mathlib.Tactic

/-!
# Low-exponent Kraft capacity and an actual eight-centre planar slice

An exponent profile uniformly at least d below the ambient exponent n
has capacity at most 2^n when there are at most 2^d actual centres.
For n >= 3, geometric centreExponent_lt_n and the exclusion of
the first TWO high exponent layers allow d=3 and eight centres.

This proves a new actual planar lower-branch subcase; it does not
establish that both high layers are absent for arbitrary AngleCap data.
-/

namespace JSP000404Research

open scoped BigOperators

/-- Uniform exponent-drop capacity, with no geometric hypotheses. -/
theorem dyadic_capacity_of_uniform_exponent_drop
    {V : Type*} [Fintype V]
    (k : V → ℕ) (n d : ℕ)
    (hd : d ≤ n)
    (hcard : Fintype.card V ≤ 2 ^ d)
    (hmax : ∀ i : V, k i ≤ n - d) :
    (∑ i : V, 2 ^ k i) ≤ 2 ^ n := by
  classical
  have hsum :
      (∑ i : V, 2 ^ k i) ≤ ∑ _i : V, 2 ^ (n - d) := by
    apply Finset.sum_le_sum
    intro i hi
    exact Nat.pow_le_pow_right (by decide : 0 < 2) (hmax i)
  calc
    (∑ i : V, 2 ^ k i) ≤ ∑ _i : V, 2 ^ (n - d) := hsum
    _ = Fintype.card V * 2 ^ (n - d) := by simp
    _ ≤ 2 ^ d * 2 ^ (n - d) :=
      Nat.mul_le_mul_right _ hcard
    _ = 2 ^ n := by
      rw [← pow_add]
      congr 1
      omega

/-- Genuine planar AngleCap certificate: at most eight original centres,
no centre in either high exponent layer n-1 and n-2. The geometric
exponent upper bound then forces all exponents <= n-3. -/
theorem planar_eight_centre_no_high_layers_capacity
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane}
    (hp : Function.Injective p)
    {lam t delta : ℝ} {n : ℕ}
    (hcap : AngleCap p lam)
    (hcard : Fintype.card V ≤ 8)
    (hn : 3 ≤ n)
    (hdelta0 : 0 ≤ delta)
    (hdeltaHalf : delta < (1 : ℝ) / 2)
    (ht : t = (n : ℝ) + delta)
    (hlam : lam = Real.pi / t)
    (C : ∀ i : V, CentreProjectiveCycle hp i)
    (hnoTop : ∀ i : V, centreExponent (C i) t ≠ n - 1)
    (hnoNext : ∀ i : V, centreExponent (C i) t ≠ n - 2) :
    (∑ i : V, 2 ^ centreExponent (C i) t) ≤ 2 ^ n := by
  have hdelta1 : delta < 1 := by linarith
  have hmax : ∀ i : V, centreExponent (C i) t ≤ n - 3 := by
    intro i
    have hi : centreExponent (C i) t < n :=
      centreExponent_lt_n
        (C i) n delta t (by omega : 1 ≤ n)
        hdelta0 hdelta1 ht
    have htop := hnoTop i
    have hnext := hnoNext i
    omega
  exact dyadic_capacity_of_uniform_exponent_drop
    (fun i : V => centreExponent (C i) t) n 3
    (by omega) (by norm_num at *; omega) hmax

/-- Necessary high-exponent obstruction for an overweight configuration
with at most eight original centres. This is a genuine geometric
contrapositive of the kernel-certified eight-centre capacity slice. -/
theorem planar_eight_centre_overweight_has_high_layer
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane}
    (hp : Function.Injective p)
    {lam t delta : ℝ} {n : ℕ}
    (hcap : AngleCap p lam)
    (hcard : Fintype.card V ≤ 8)
    (hn : 3 ≤ n)
    (hdelta0 : 0 ≤ delta)
    (hdeltaHalf : delta < (1 : ℝ) / 2)
    (ht : t = (n : ℝ) + delta)
    (hlam : lam = Real.pi / t)
    (C : ∀ i : V, CentreProjectiveCycle hp i)
    (hover : 2 ^ n < ∑ i : V, 2 ^ centreExponent (C i) t) :
    ∃ i : V, centreExponent (C i) t = n - 1 ∨
      centreExponent (C i) t = n - 2 := by
  classical
  by_contra h
  have hnoTop : ∀ i : V, centreExponent (C i) t ≠ n - 1 := by
    intro i heq
    exact h ⟨i, Or.inl heq⟩
  have hnoNext : ∀ i : V, centreExponent (C i) t ≠ n - 2 := by
    intro i heq
    exact h ⟨i, Or.inr heq⟩
  have hcapBound :=
    planar_eight_centre_no_high_layers_capacity
      hp hcap hcard hn hdelta0 hdeltaHalf ht hlam
      C hnoTop hnoNext
  omega

#print axioms dyadic_capacity_of_uniform_exponent_drop
#print axioms planar_eight_centre_no_high_layers_capacity
#print axioms planar_eight_centre_overweight_has_high_layer

end JSP000404Research
