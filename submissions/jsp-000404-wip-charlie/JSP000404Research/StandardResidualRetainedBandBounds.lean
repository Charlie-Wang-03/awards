import JSP000404Research.StandardResidual
import Mathlib.Tactic

/-!
# Exact band bounds for a retained standard-residual edge

This is the lightweight local fact needed by retained-angle arguments.
It is intentionally separated from the heavier three-band and support-one
modules.

For an increasing retained edge of the standard (n+1)-band colouring, its
normalized direction lies in the unit interval indexed by its retained colour.
-/

namespace JSP000404Research
namespace DirectionData

open OrderedEdgeColoring

theorem standardResidual_retained_edge_exact_band_bounds
    {V : Type*} [LinearOrder V]
    {width : ℝ}
    (D : DirectionData V width)
    {n : ℕ}
    (hwidth : width < (n + 1 : ℕ))
    {u v : V}
    (huv : u < v)
    (hret :
      ((standardResidualColoring D n hwidth).color u v).val < n) :
    let c :=
      retainedColor
        (standardResidualColoring D n hwidth) u v hret
    (c.val : ℝ) ≤ D.value u v ∧
      D.value u v < (c.val : ℝ) + 1 := by
  let R := standardResidualColoring D n hwidth
  let c : Fin n := retainedColor R u v hret
  have hfull :
      R.color u v = c.castSucc := by
    apply Fin.ext
    simp [R,c,retainedColor]
  have hband :=
    (standardBandColor_eq_iff
      D (n + 1) (Nat.succ_pos n)
      (by exact_mod_cast hwidth)
      huv c.castSucc).1
      (by simpa [R,standardResidualColoring] using hfull)
  simpa [c] using hband

#print axioms standardResidual_retained_edge_exact_band_bounds

end DirectionData
end JSP000404Research
