
import JSP000404Research.ResidualLocalSaturation
import JSP000404Research.ResidualUnsafeEdgeBudget
import Mathlib.Tactic

/-!
# Unsafe saturated residual pairs force zero wrap excess at one endpoint

Let R be the standard residual (n+1)-band colouring of DirectionData D and
let u<v be a residual edge.

If the edge is unsafe, its residual forbidden set is all retained colours:

  incomingRetained(u) union outgoingRetained(v) = Fin n.

Hence retained colour zero belongs either to incomingRetained(u) or to
outgoingRetained(v).  In either case full standard band zero is active at the
corresponding endpoint.

If both endpoint local cycles are projected-saturated, both also see the
residual top band n.  ResidualLocalSaturation and LinearBandSaturation then
force zero cyclic wrap excess at whichever endpoint sees band zero.

Thus every unsafe saturated--saturated carrier has a concrete zero-wrap
endpoint.
-/

namespace JSP000404Research
namespace DirectionData

open OrderedEdgeColoring

def HasZeroWrapExcess
    {V : Type*} [LinearOrder V] [Fintype V]
    {t : ℝ}
    {D : DirectionData V t}
    {v : V}
    (L : LocalDirectionCycle D v) : Prop :=
  ∃ a xs,
    L.values = a :: xs ∧
    excess
      (Nat.floor
        (a + t - xs.getLastD a))
      =
    0

theorem hasZeroWrapExcess_of_saturated_zero_band
    {V : Type*} [LinearOrder V] [Fintype V]
    {t : ℝ} {n : ℕ}
    (D : DirectionData V t)
    (L : LocalDirectionCycle D v)
    (hwidth : t < (n + 1 : ℕ))
    (hn : 1 ≤ n)
    (hsat :
      L.exponent =
        projectedFree (standardResidualColoring D n hwidth) v)
    (hres :
      residualCoord n ∈
        active (standardResidualColoring D n hwidth) v)
    (hzero :
      (0 : Fin (n + 1)) ∈
        active (standardResidualColoring D n hwidth) v) :
    HasZeroWrapExcess L := by
  obtain ⟨a, xs, hvalues, _ha0, _hsorted, _hall,
      _hzeroOcc, _htop, _hfull, hwrap⟩ :=
    exists_saturated_zero_wrap_value_decomposition
      D L hwidth hn hsat hres hzero
  exact ⟨a, xs, hvalues, hwrap⟩

/-- Main unsafe saturated-pair rigidity. -/
theorem unsafe_residual_saturated_pair_has_zero_wrap_endpoint
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
          (standardResidualColoring D n hwidth) v) :
    HasZeroWrapExcess Lu ∨ HasZeroWrapExcess Lv := by
  let R := standardResidualColoring D n hwidth
  have hresActive :=
    residualCoord_mem_active_of_isResidual
      R huv hres
  have hzeroUnion :
      (0 : Fin n) ∈
        incomingRetained R u ∪ outgoingRetained R v := by
    rw [unsafe_residual_union_eq_univ R hunsafe]
    simp
  rcases Finset.mem_union.mp hzeroUnion with hzeroIn | hzeroOut
  · left
    have hzeroRet :
        (0 : Fin n) ∈ retainedActive R u :=
      incomingRetained_subset_retainedActive
        R u hzeroIn
    have hzeroFull :
        (0 : Fin (n + 1)) ∈ active R u := by
      have hcast :=
        (castSucc_mem_active_iff_mem_retainedActive
          R u (0 : Fin n)).2 hzeroRet
      simpa using hcast
    exact hasZeroWrapExcess_of_saturated_zero_band
      D Lu hwidth hn hsatU hresActive.1 hzeroFull
  · right
    have hzeroRet :
        (0 : Fin n) ∈ retainedActive R v :=
      outgoingRetained_subset_retainedActive
        R v hzeroOut
    have hzeroFull :
        (0 : Fin (n + 1)) ∈ active R v := by
      have hcast :=
        (castSucc_mem_active_iff_mem_retainedActive
          R v (0 : Fin n)).2 hzeroRet
      simpa using hcast
    exact hasZeroWrapExcess_of_saturated_zero_band
      D Lv hwidth hn hsatV hresActive.2 hzeroFull

#print axioms hasZeroWrapExcess_of_saturated_zero_band
#print axioms unsafe_residual_saturated_pair_has_zero_wrap_endpoint

end DirectionData
end JSP000404Research
