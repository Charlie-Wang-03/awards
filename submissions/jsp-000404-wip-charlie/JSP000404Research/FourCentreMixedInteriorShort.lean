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
  have hnat : n - 1 + 1 = n :=
    Nat.sub_add_cancel hn
  have hcast :
      ((n - 1 : ℕ) : ℝ) + 1 = (n : ℝ) := by
    exact_mod_cast hnat
  have hncast :
      ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
    linarith
  have hlower :
      2 * lam ≤ p + u + z + v := by
    linarith
  have hupper0 :
      p + u + z + v ≤ Real.pi - w := by
    linarith [houter]
  have hupper1 :
      Real.pi - w ≤ (1 + delta) * lam := by
    rw [hpi, ht]
    rw [hncast] at hw
    nlinarith
  have hstrict :
      (1 + delta) * lam < 2 * lam := by
    nlinarith
  linarith


/-- The interior terminal only needs the hidden angle up to one remainder
loss delta*lambda.  This is the form naturally produced if the hidden
(n-1)-quotient belongs to the outer angle s-b-a while the complementary
a-b-c angle is at most delta*lambda. -/
theorem mixed_four_interior_short_arithmetic_contradiction_weakened
    {lam t delta As Aa Ab p u v w z : ℝ}
    {n : ℕ}
    (hn : 1 ≤ n)
    (hlampos : 0 < lam)
    (hdelta0 : 0 ≤ delta)
    (hdeltaHalf : delta < (1 : ℝ) / 2)
    (ht : t = (n : ℝ) + delta)
    (hpi : Real.pi = t * lam)
    (houter : As + Aa + Ab = Real.pi)
    (hp : p ≤ As)
    (huv : u + v ≤ Aa)
    (hwz : w + z ≤ Ab)
    (hw :
      (((n - 1 : ℕ) : ℝ) - delta) * lam ≤ w)
    (hpu : lam ≤ p + u)
    (hzv : lam ≤ z + v) :
    False := by
  have hnat : n - 1 + 1 = n :=
    Nat.sub_add_cancel hn
  have hcast :
      ((n - 1 : ℕ) : ℝ) + 1 = (n : ℝ) := by
    exact_mod_cast hnat
  have hncast :
      ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
    linarith
  have hlower :
      2 * lam ≤ p + u + z + v := by
    linarith
  have hupper0 :
      p + u + z + v ≤ Real.pi - w := by
    linarith [houter]
  have hupper1 :
      Real.pi - w ≤ (1 + 2 * delta) * lam := by
    rw [hpi, ht]
    rw [hncast] at hw
    nlinarith
  have hstrict :
      (1 + 2 * delta) * lam < 2 * lam := by
    nlinarith
  linarith

#print axioms mixed_four_interior_short_arithmetic_contradiction
#print axioms mixed_four_interior_short_arithmetic_contradiction_weakened

end JSP000404Research
