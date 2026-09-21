import Mathlib.Tactic

/-!
# Short arithmetic terminal for the mixed four-centre interior branch

The earlier interior outlet tracked three normalized exterior turns.  A shorter
terminal is available.

Let As,Aa,Ab be the three angles of the outer triangle s-a-b.  Let the interior
point c split the relevant angles into

  p <= As,
  u+v <= Aa,
  w+z <= Ab.

The global cap on triangles s-a-c and a-b-c gives

  lambda <= p+u,
  lambda <= z+v.

If the hidden positive quotient n-1 at the support-two centre b is realized by
the interior angle w = angle(s,b,c), then

  (n-1)*lambda <= w.

Since As+Aa+Ab=pi=t*lambda and t=n+delta,

  p+u+z+v <= pi-w <= (1+delta)*lambda < 2*lambda,

contradicting the two cap lower bounds.

This formulation avoids explicit exterior-turn variables and isolates the
remaining geometry to identifying the hidden n-1 gap with angle(s,b,c).
-/

namespace JSP000404Research

open Real

theorem mixed_four_interior_short_arithmetic_contradiction
    {lam t delta As Aa Ab p u v w z : ℝ}
    {n : ℕ}
    (hlampos : 0 < lam)
    (hdelta : delta < 1)
    (ht : t = (n : ℝ) + delta)
    (hpi : Real.pi = t * lam)
    (houter : As + Aa + Ab = Real.pi)
    (hp : p ≤ As)
    (huv : u + v ≤ Aa)
    (hwz : w + z ≤ Ab)
    (hw : ((n - 1 : ℕ) : ℝ) * lam ≤ w)
    (hpu : lam ≤ p + u)
    (hzv : lam ≤ z + v) :
    False := by
  have hncast :
      (((n - 1 : ℕ) : ℕ) : ℝ) ≥ (n : ℝ) - 1 := by
    by_cases hn0 : n = 0
    · subst n
      norm_num
    · have hn1 : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr hn0
      exact_mod_cast (Nat.sub_add_cancel hn1).le
  have hlower :
      2 * lam ≤ p + u + z + v := by
    linarith
  have hupper0 :
      p + u + z + v ≤ Real.pi - w := by
    linarith [houter]
  have hupper1 :
      Real.pi - w ≤ (1 + delta) * lam := by
    rw [hpi, ht]
    have hw' :
        ((n : ℝ) - 1) * lam ≤ w := by
      have hmul :=
        mul_le_mul_of_nonneg_right hncast hlampos.le
      exact hmul.trans hw
    nlinarith
  have hstrict :
      (1 + delta) * lam < 2 * lam := by
    nlinarith
  linarith

/-- Cleaner form when n>=1, so the cast of n-1 is exact. -/
theorem mixed_four_interior_short_arithmetic_contradiction_of_one_le
    {lam t delta As Aa Ab p u v w z : ℝ}
    {n : ℕ}
    (hn : 1 ≤ n)
    (hlampos : 0 < lam)
    (hdelta : delta < 1)
    (ht : t = (n : ℝ) + delta)
    (hpi : Real.pi = t * lam)
    (houter : As + Aa + Ab = Real.pi)
    (hp : p ≤ As)
    (huv : u + v ≤ Aa)
    (hwz : w + z ≤ Ab)
    (hw : ((n - 1 : ℕ) : ℝ) * lam ≤ w)
    (hpu : lam ≤ p + u)
    (hzv : lam ≤ z + v) :
    False := by
  exact mixed_four_interior_short_arithmetic_contradiction
    hlampos hdelta ht hpi houter hp huv hwz hw hpu hzv

#print axioms mixed_four_interior_short_arithmetic_contradiction
#print axioms mixed_four_interior_short_arithmetic_contradiction_of_one_le

end JSP000404Research
