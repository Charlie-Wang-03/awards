import JSP000404Research.CyclicBandPhaseSlip
import JSP000404Research.StandardResidual
import JSP000404Research.ResidualActiveDrop
import Mathlib.Tactic

/-!
# Wrap unit jumps force activity of the residual top direction band

For a sorted cyclic list in standard bands 0,...,n, the final wrap
jump equals (n+1-floor(last))+floor(first).

A wrap jump of size one therefore forces floor(last)=n and
floor(first)=0.  Applied to a genuine LocalDirectionCycle,
this yields an actual incident edge occupying the top (residual)
standard band.  This distinguishes wrap phase slips from interior
phase slips at centres where the residual colour is inactive.

This is a genuine link from cyclic gap geometry to the existing
ResidualActiveDrop / recolouring interface; it does not assert that
all troublesome phase slips occur at the wrap.
-/

namespace JSP000404Research

/-- A unit jump across the cyclic wrap requires the two extremal
labels of the entire n+1-unit-band palette. -/
theorem wrap_unit_band_jump_forces_extreme_labels
    (n : ℕ) (a last : ℝ)
    (hlast : Nat.floor last ≤ n)
    (hwrap : (n + 1 - Nat.floor last) + Nat.floor a = 1) :
    Nat.floor last = n ∧ Nat.floor a = 0 := by
  omega

namespace DirectionData
namespace LocalDirectionCycle

open OrderedEdgeColoring

/-- A cyclic wrap jump of size one forces the actual standard residual
colour n to be active at the centre. In particular, a wrap (0,1)
phase slip cannot occur at a residual-inactive centre. -/
theorem residual_active_of_wrap_unit_band_jump
    {V : Type*} [LinearOrder V] [Fintype V]
    {t : ℝ} {n : ℕ}
    {D : DirectionData V t} {i : V}
    (C : LocalDirectionCycle D i)
    (ht : t < (n : ℝ) + 1)
    (a : ℝ) (xs : List ℝ)
    (hvalues : C.values = a :: xs)
    (hwrap :
      (n + 1 - Nat.floor (xs.getLastD a)) +
        Nat.floor a = 1) :
    residualCoord n ∈
      active
        (standardResidualColoring D n
          (by exact_mod_cast ht)) i := by
  classical
  have hlastMem : xs.getLastD a ∈ C.values := by
    rw [hvalues]
    exact List.getLastD_mem_cons
  have hlastBounds := C.value_mem_bounds hlastMem
  have hlastFloor : Nat.floor (xs.getLastD a) ≤ n :=
    floorLabel_le_n_of_lt_n_succ hlastBounds.1
      (hlastBounds.2.trans ht)
  have htop :=
    (wrap_unit_band_jump_forces_extreme_labels
      n a (xs.getLastD a) hlastFloor hwrap).1
  have hocc : n ∈ occupiedNatBands C.values := by
    change n ∈ (C.values.map Nat.floor).toFinset
    apply List.mem_toFinset.mpr
    exact List.mem_map.mpr
      ⟨xs.getLastD a, hlastMem, htop⟩
  have hwidth : t ≤ ((n + 1 : ℕ) : ℝ) := by
    have hx : t < ((n + 1 : ℕ) : ℝ) := by
      simpa [Nat.cast_add, Nat.cast_one] using ht
    exact le_of_lt hx
  have heq :=
    C.occupiedNatBands_values_eq_incident_val_map
      (n + 1) hwidth
  rw [heq] at hocc
  obtain ⟨c, hc, hval⟩ := Finset.mem_map.mp hocc
  have hvaln : c.val = n := by
    simpa using hval
  have hcEq : c = residualCoord n := by
    apply Fin.ext
    simpa [residualCoord] using hvaln
  have hres : residualCoord n ∈ D.incidentBands (n + 1) i :=
    hcEq ▸ hc
  simpa only [standardResidual_active_eq_incidentBands_succ] using hres

/-- If the residual top band is inactive, the cyclic wrap jump
is not one; therefore any necessary phase slip of a saturated
centre must arise in a non-wrap position. -/
theorem wrap_jump_ne_one_of_residual_inactive
    {V : Type*} [LinearOrder V] [Fintype V]
    {t : ℝ} {n : ℕ}
    {D : DirectionData V t} {i : V}
    (C : LocalDirectionCycle D i)
    (ht : t < (n : ℝ) + 1)
    (a : ℝ) (xs : List ℝ)
    (hvalues : C.values = a :: xs)
    (hres : residualCoord n ∉
      active (standardResidualColoring D n
        (by exact_mod_cast ht)) i) :
    (n + 1 - Nat.floor (xs.getLastD a)) +
      Nat.floor a ≠ 1 := by
  intro hwrap
  exact hres
    (C.residual_active_of_wrap_unit_band_jump
      ht a xs hvalues hwrap)

#print axioms wrap_unit_band_jump_forces_extreme_labels
#print axioms LocalDirectionCycle.residual_active_of_wrap_unit_band_jump
#print axioms LocalDirectionCycle.wrap_jump_ne_one_of_residual_inactive

end LocalDirectionCycle
end DirectionData
end JSP000404Research
