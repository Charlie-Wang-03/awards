import JSP000404Research.CyclicWrapSlipResidual
import Mathlib.Tactic

/-!
# Residual-inactive saturated centres must have an interior phase slip

At every saturated local centre, the paired cyclic real-gap-floor
and integer-band-jump lists contain (0,1).

The cyclic pair list consists of the paired successive interior gaps
and the single wrap pair. The latter is impossible when the residual
top colour is inactive, since a wrap unit jump activates that colour.

Hence a saturated residual-inactive centre contains two *successive*
interior directions with real gap shorter than one unit while
their floor-band labels differ by exactly one.

The conclusion is a geometric local obstruction for further
cross-centre triangle arguments, not a contradiction in itself.
-/

namespace JSP000404Research

/-- Appending one aligned pair to two pointwise-related lists
appends precisely that pair to their zip. -/
theorem zip_append_one_of_forall₂_le
    {xs ys : List ℕ}
    (h : List.Forall₂ (· ≤ ·) xs ys)
    (a b : ℕ) :
    List.zip (xs ++ [a]) (ys ++ [b]) =
      List.zip xs ys ++ [(a, b)] := by
  induction h with
  | nil =>
      simp
  | @cons x y xs ys _ _ ih =>
      simp [ih]

namespace DirectionData
namespace LocalDirectionCycle

open OrderedEdgeColoring

/-- Decomposition of concrete cyclic floor-gap/band-jump pairs into
successive interior pairs followed by one wrap pair. -/
theorem cyclic_floor_band_zip_eq_interior_append_wrap
    {V : Type*} [LinearOrder V] [Fintype V]
    {t : ℝ} {n : ℕ}
    {D : DirectionData V t} {i : V}
    (C : LocalDirectionCycle D i)
    (ht : t < (n : ℝ) + 1)
    (a : ℝ) (xs : List ℝ)
    (hvalues : C.values = a :: xs) :
    List.zip
        ((cyclicRealGapsAt t C.values).map Nat.floor)
        (cyclicBandJumps n (C.values.map Nat.floor)) =
      List.zip
          ((successiveDiffsFrom a xs).map Nat.floor)
          (successiveNatDiffsFrom (Nat.floor a) (xs.map Nat.floor)) ++
        [(Nat.floor (a + t - xs.getLastD a),
          (n + 1 - Nat.floor (xs.getLastD a)) + Nat.floor a)] := by
  have hsorted : (a :: xs).Pairwise (· ≤ ·) := by
    simpa [hvalues] using C.values_pairwise
  have ha0 : 0 ≤ a :=
    (C.value_mem_bounds (by simp [hvalues])).1
  have hinter :=
    successiveFloorDiffs_le_successiveBandJumps
      a xs ha0 hsorted
  rw [hvalues]
  simp only [cyclicRealGapsAt, cyclicBandJumps,
    List.map_append, List.map_cons, List.map_nil, map_getLastD_eq]
  exact zip_append_one_of_forall₂_le hinter _ _

/-- A saturated centre which does not use the residual colour
necessarily has a *non-wrap* adjacent (0,1) phase slip. -/
theorem interior_phase_slip_of_tight_and_residual_inactive
    {V : Type*} [LinearOrder V] [Fintype V]
    {t : ℝ} {n : ℕ}
    {D : DirectionData V t} {i : V}
    (C : LocalDirectionCycle D i)
    (ht : t < (n : ℝ) + 1)
    (a : ℝ) (xs : List ℝ)
    (hvalues : C.values = a :: xs)
    (htight :
      C.exponent + (D.incidentBands (n + 1) i).card = n + 1)
    (hres : residualCoord n ∉
      active (standardResidualColoring D n
        (by exact_mod_cast ht)) i) :
    (0, 1) ∈ List.zip
      ((successiveDiffsFrom a xs).map Nat.floor)
      (successiveNatDiffsFrom (Nat.floor a) (xs.map Nat.floor)) := by
  have hphase :=
    C.has_floor_zero_unit_band_jump_of_local_tight ht htight
  have hzip :=
    C.cyclic_floor_band_zip_eq_interior_append_wrap
      ht a xs hvalues
  rw [hzip] at hphase
  rcases List.mem_append.mp hphase with hinter | hwrap
  · exact hinter
  · have hpair :
        (0, 1) =
          (Nat.floor (a + t - xs.getLastD a),
            (n + 1 - Nat.floor (xs.getLastD a)) + Nat.floor a) := by
      simpa only [List.mem_singleton] using hwrap
    have hunit :
        (n + 1 - Nat.floor (xs.getLastD a)) + Nat.floor a = 1 := by
      have h := congrArg Prod.snd hpair
      simpa using h.symm
    exact False.elim
      (hres (C.residual_active_of_wrap_unit_band_jump
        ht a xs hvalues hunit))

#print axioms zip_append_one_of_forall₂_le
#print axioms LocalDirectionCycle.cyclic_floor_band_zip_eq_interior_append_wrap
#print axioms LocalDirectionCycle.interior_phase_slip_of_tight_and_residual_inactive

end LocalDirectionCycle
end DirectionData
end JSP000404Research
