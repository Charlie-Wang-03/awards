import JSP000404Research.ResidualUnsafeSaturatedWrap
import Mathlib.Tactic

/-!
# Zero wrap excess forces the first occupied band to be zero

For one nonempty local direction cycle, saturated wrap rigidity has the form

  excess(floor(a + t - last)) = floor(a).

If the same cycle also has zero wrap excess, then its unique list
decomposition has

  excess(floor(a + t - last)) = 0.

Therefore floor(a)=0.

The only small technical point is that the two hypotheses may present the
same nonempty value list through two existential decompositions.  Equality of
the list forces the two heads and tails to coincide.
-/

namespace JSP000404Research
namespace DirectionData

/-- A fixed saturated wrap decomposition of a cycle with zero wrap excess
must start in natural band zero. -/
theorem floor_head_eq_zero_of_wrap_rigidity_of_zeroWrap
    {V : Type*} [LinearOrder V] [Fintype V]
    {t : ℝ}
    {D : DirectionData V t}
    {v : V}
    (L : LocalDirectionCycle D v)
    {a : ℝ} {xs : List ℝ}
    (hvalues : L.values = a :: xs)
    (hwrap :
      excess
        (Nat.floor
          (a + t - xs.getLastD a))
        =
      Nat.floor a)
    (hzero : HasZeroWrapExcess L) :
    Nat.floor a = 0 := by
  obtain ⟨a0, xs0, hvalues0, hwrap0⟩ := hzero
  have hcons :
      a :: xs = a0 :: xs0 :=
    hvalues.symm.trans hvalues0
  have ha : a = a0 :=
    (List.cons.inj hcons).1
  have hxs : xs = xs0 :=
    (List.cons.inj hcons).2
  subst a0
  subst xs0
  omega

/-- Equivalent formulation: the saturated wrap excess itself is zero. -/
theorem saturated_wrap_excess_eq_zero_of_zeroWrap
    {V : Type*} [LinearOrder V] [Fintype V]
    {t : ℝ}
    {D : DirectionData V t}
    {v : V}
    (L : LocalDirectionCycle D v)
    {a : ℝ} {xs : List ℝ}
    (hvalues : L.values = a :: xs)
    (hwrap :
      excess
        (Nat.floor
          (a + t - xs.getLastD a))
        =
      Nat.floor a)
    (hzero : HasZeroWrapExcess L) :
    excess
      (Nat.floor
        (a + t - xs.getLastD a))
      =
    0 := by
  rw [hwrap]
  exact floor_head_eq_zero_of_wrap_rigidity_of_zeroWrap
    L hvalues hwrap hzero

#print axioms floor_head_eq_zero_of_wrap_rigidity_of_zeroWrap
#print axioms saturated_wrap_excess_eq_zero_of_zeroWrap

end DirectionData
end JSP000404Research
