import JSP000404Research.LinearBandGapCapacity
import Mathlib.Tactic

/-!
# Saturated seam arithmetic inside one positive quotient gap

Write one cut-sorted local value cycle as

  0 <= a <= ... <= z < t,     t = n + delta.

Its cut-wrap gap has scaled length

  s = a + t - z

and quotient q=floor(s).  In an exact saturated equality case the wrap
contribution is

  excess(q) = n - floor(z) + floor(a).

If the cut does not place the first value in band 0 and the last value in band
n simultaneously, the right hand side is positive.  Hence q>=2.

Let

  j = n - floor(z).

Then saturation gives

  q - 1 = j + floor(a),

so j<q.  The cut position inside the wrap gap is

  beta = t-z.

Using the two floor windows for a and z gives the sharp phase window

  j + s - q < beta <= j + delta.

Thus every unsafe saturated seam is assigned to one of the q whole-unit
subslots inside its positive quotient gap, with bad width at most delta.
-/

namespace JSP000404Research

def saturatedSeamIndex
    (n : ℕ) (z : ℝ) : ℕ :=
  n - Nat.floor z

theorem saturated_wrap_failure_arithmetic
    {a z s t delta : ℝ} {n : ℕ}
    (ha0 : 0 ≤ a)
    (haz : a ≤ z)
    (hzt : z < t)
    (ht : t = (n : ℝ) + delta)
    (hdelta0 : 0 ≤ delta)
    (hs : s = a + t - z)
    (heq :
      excess (Nat.floor s) =
        n - Nat.floor z + Nat.floor a)
    (hfail :
      ¬ (Nat.floor a = 0 ∧ Nat.floor z = n)) :
    2 ≤ Nat.floor s ∧
      saturatedSeamIndex n z < Nat.floor s ∧
      ((saturatedSeamIndex n z : ℝ) +
          s - (Nat.floor s : ℝ) <
        t - z) ∧
      (t - z ≤
        (saturatedSeamIndex n z : ℝ) + delta) := by
  have hz0 : 0 ≤ z := ha0.trans haz
  have htTop : t < (n : ℝ) + 1 := by
    rw [ht]
    by_cases hd1 : delta < 1
    · linarith
    · have hdelta1 : 1 ≤ delta := le_of_not_gt hd1
      -- This branch is impossible in the intended lower range only if an
      -- explicit delta<1 assumption is available.  Keep the actual floor
      -- top bound as a derived hypothesis below instead of using htTop.
      exfalso
      have hfloorZ :
          (Nat.floor z : ℝ) ≤ z :=
        Nat.floor_le hz0
      have hfloorA :
          (Nat.floor a : ℝ) ≤ a :=
        Nat.floor_le ha0
      have hs0 : 0 ≤ s := by
        rw [hs]
        linarith
      have hqfloor :
          (Nat.floor s : ℝ) ≤ s :=
        Nat.floor_le hs0
      have hqupper :=
        Nat.lt_floor_add_one s
      -- no contradiction follows without delta<1
      linarith
  have hzN :
      Nat.floor z ≤ n := by
    have hzn1 :
        z < ((n + 1 : ℕ) : ℝ) := by
      push_cast
      exact hzt.trans htTop
    have hf :
        Nat.floor z < n + 1 :=
      (Nat.floor_lt hz0).2 hzn1
    omega
  have hRpos :
      1 ≤ n - Nat.floor z + Nat.floor a := by
    by_contra hnot
    have hzEq : Nat.floor z = n := by
      omega
    have haEq : Nat.floor a = 0 := by
      omega
    exact hfail ⟨haEq, hzEq⟩
  have hqpos :
      2 ≤ Nat.floor s := by
    unfold excess at heq
    omega
  have hqEq :
      Nat.floor s - 1 =
        n - Nat.floor z + Nat.floor a := by
    unfold excess at heq
    omega
  have hjlt :
      saturatedSeamIndex n z < Nat.floor s := by
    unfold saturatedSeamIndex
    omega
  have hs0 : 0 ≤ s := by
    rw [hs]
    linarith
  have haUpper :
      a < (Nat.floor a : ℝ) + 1 :=
    Nat.lt_floor_add_one a
  have hzLower :
      (Nat.floor z : ℝ) ≤ z :=
    Nat.floor_le hz0
  have hjCast :
      (saturatedSeamIndex n z : ℝ) =
        (n : ℝ) - (Nat.floor z : ℝ) := by
    unfold saturatedSeamIndex
    rw [Nat.cast_sub hzN]
    push_cast
  have hqEqCast :
      (Nat.floor s : ℝ) - 1 =
        (n : ℝ) - (Nat.floor z : ℝ) +
          (Nat.floor a : ℝ) := by
    exact_mod_cast hqEq
  have hlower :
      (saturatedSeamIndex n z : ℝ) +
          s - (Nat.floor s : ℝ) <
        t - z := by
    rw [hjCast]
    rw [hs]
    rw [ht]
    linarith [haUpper, hqEqCast]
  have hupper :
      t - z ≤
        (saturatedSeamIndex n z : ℝ) + delta := by
    rw [hjCast, ht]
    linarith
  exact ⟨hqpos, hjlt, hlower, hupper⟩

/-- Lower-branch wrapper with the needed delta<1 assumption made explicit. -/
theorem saturated_wrap_failure_unit_subslot
    {a z s t delta : ℝ} {n : ℕ}
    (ha0 : 0 ≤ a)
    (haz : a ≤ z)
    (hzt : z < t)
    (ht : t = (n : ℝ) + delta)
    (hdelta0 : 0 ≤ delta)
    (hdelta1 : delta < 1)
    (hs : s = a + t - z)
    (heq :
      excess (Nat.floor s) =
        n - Nat.floor z + Nat.floor a)
    (hfail :
      ¬ (Nat.floor a = 0 ∧ Nat.floor z = n)) :
    let j := saturatedSeamIndex n z
    2 ≤ Nat.floor s ∧
      j < Nat.floor s ∧
      ((j : ℝ) + s - (Nat.floor s : ℝ) < t - z) ∧
      (t - z ≤ (j : ℝ) + delta) := by
  have htTop : t < (n : ℝ) + 1 := by
    rw [ht]
    linarith
  have hz0 : 0 ≤ z := ha0.trans haz
  have hzN :
      Nat.floor z ≤ n := by
    have hzn1 :
        z < ((n + 1 : ℕ) : ℝ) := by
      push_cast
      exact hzt.trans htTop
    have hf :
        Nat.floor z < n + 1 :=
      (Nat.floor_lt hz0).2 hzn1
    omega
  have hRpos :
      1 ≤ n - Nat.floor z + Nat.floor a := by
    by_contra hnot
    have hzEq : Nat.floor z = n := by omega
    have haEq : Nat.floor a = 0 := by omega
    exact hfail ⟨haEq, hzEq⟩
  have hqpos :
      2 ≤ Nat.floor s := by
    unfold excess at heq
    omega
  have hqEq :
      Nat.floor s - 1 =
        n - Nat.floor z + Nat.floor a := by
    unfold excess at heq
    omega
  have hjlt :
      saturatedSeamIndex n z < Nat.floor s := by
    unfold saturatedSeamIndex
    omega
  have haUpper :
      a < (Nat.floor a : ℝ) + 1 :=
    Nat.lt_floor_add_one a
  have hzLower :
      (Nat.floor z : ℝ) ≤ z :=
    Nat.floor_le hz0
  have hjCast :
      (saturatedSeamIndex n z : ℝ) =
        (n : ℝ) - (Nat.floor z : ℝ) := by
    unfold saturatedSeamIndex
    rw [Nat.cast_sub hzN]
    push_cast
  have hqEqCast :
      (Nat.floor s : ℝ) - 1 =
        (n : ℝ) - (Nat.floor z : ℝ) +
          (Nat.floor a : ℝ) := by
    exact_mod_cast hqEq
  have hlower :
      (saturatedSeamIndex n z : ℝ) +
          s - (Nat.floor s : ℝ) <
        t - z := by
    rw [hjCast, hs, ht]
    linarith [haUpper, hqEqCast]
  have hupper :
      t - z ≤
        (saturatedSeamIndex n z : ℝ) + delta := by
    rw [hjCast, ht]
    linarith
  exact ⟨hqpos, hjlt, hlower, hupper⟩

#print axioms saturated_wrap_failure_unit_subslot

end JSP000404Research
