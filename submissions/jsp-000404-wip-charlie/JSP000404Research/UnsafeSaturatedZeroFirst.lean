import JSP000404Research.ZeroWrapFirstBand
import Mathlib.Tactic

/-!
# Unsafe saturated residual pairs have a zero-first endpoint

ResidualUnsafeSaturatedWrap proves that an unsafe residual pair whose two
local cycles are projected-saturated has zero cyclic wrap excess at at least
one endpoint.

If both endpoints also carry the standard saturated wrap rigidity

  excess(floor(a+t-last)) = floor(a),

then ZeroWrapFirstBand converts zero wrap excess into

  floor(a)=0.

Thus every unsafe saturated pair has at least one endpoint whose sorted local
cycle begins in natural band zero.
-/

namespace JSP000404Research
namespace DirectionData

open OrderedEdgeColoring

theorem unsafe_saturated_pair_has_zeroFirst_endpoint
    {V : Type*} [LinearOrder V] [Fintype V]
    {t : ℝ} {n : ℕ}
    (D : DirectionData V t)
    (hwidth : t < (n + 1 : ℕ))
    (hn : 1 ≤ n)
    {u v : V}
    (huv : u < v)
    (hres :
      IsResidual (standardResidualColoring D n hwidth) u v)
    (hunsafe :
      ¬ ∃ c : Fin n,
        c ∉ residualForbidden
          (standardResidualColoring D n hwidth) u v)
    (Lu : LocalDirectionCycle D u)
    (Lv : LocalDirectionCycle D v)
    (hsatU :
      Lu.exponent =
        projectedFree
          (standardResidualColoring D n hwidth) u)
    (hsatV :
      Lv.exponent =
        projectedFree
          (standardResidualColoring D n hwidth) v)
    (huRigid :
      ∃ a xs,
        Lu.values = a :: xs ∧
        excess
          (Nat.floor
            (a + t - xs.getLastD a))
          =
        Nat.floor a)
    (hvRigid :
      ∃ a xs,
        Lv.values = a :: xs ∧
        excess
          (Nat.floor
            (a + t - xs.getLastD a))
          =
        Nat.floor a) :
    (∃ a xs,
      Lu.values = a :: xs ∧
      excess
        (Nat.floor
          (a + t - xs.getLastD a))
        =
      Nat.floor a ∧
      Nat.floor a = 0)
    ∨
    (∃ a xs,
      Lv.values = a :: xs ∧
      excess
        (Nat.floor
          (a + t - xs.getLastD a))
        =
      Nat.floor a ∧
      Nat.floor a = 0) := by
  have hzero :=
    unsafe_residual_saturated_pair_has_zero_wrap_endpoint
      D hwidth hn huv hres hunsafe
      Lu Lv hsatU hsatV
  rcases hzero with hzeroU | hzeroV
  · left
    obtain ⟨a, xs, hvalues, hwrap⟩ := huRigid
    refine ⟨a, xs, hvalues, hwrap, ?_⟩
    exact floor_head_eq_zero_of_wrap_rigidity_of_zeroWrap
      Lu hvalues hwrap hzeroU
  · right
    obtain ⟨a, xs, hvalues, hwrap⟩ := hvRigid
    refine ⟨a, xs, hvalues, hwrap, ?_⟩
    exact floor_head_eq_zero_of_wrap_rigidity_of_zeroWrap
      Lv hvalues hwrap hzeroV

#print axioms unsafe_saturated_pair_has_zeroFirst_endpoint

end DirectionData
end JSP000404Research
