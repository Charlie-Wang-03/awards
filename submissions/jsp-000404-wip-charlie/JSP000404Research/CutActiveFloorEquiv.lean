import JSP000404Research.CutSaturatedEndpointDichotomy
import Mathlib.Tactic

/-!
# Exact active-band / cut-value-floor equivalence

For a CentreCutRayCycle R at the same projective cut as
cutProjectiveBandPartition, an old band b is active at the centre iff some
normalized cut-ray value in R has natural floor b.val.

This completes the one-way helper active_of_normalizedValue_floor and gives a
clean interface for transporting old-palette equalities between centres.
-/

namespace JSP000404Research

open BinaryEdgePartition

theorem active_iff_exists_normalizedValue_floor
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane} (hp : Function.Injective p)
    (hcap : AngleCap p lam)
    {lam t c : ℝ}
    (ht : 0 < t)
    (hlam : lam = Real.pi / t)
    (hc0 : 0 ≤ c) (hcpi : c < Real.pi)
    (n : ℕ)
    (htop : t < (n + 1 : ℕ))
    {i : V}
    (C : CentreProjectiveCycle hp i)
    (R : CentreCutRayCycle hp C c)
    (b : Fin (n + 1)) :
    b ∈
        active
          (cutProjectiveBandPartition
            hp hcap ht hlam hc0 hcpi n htop)
          i
      ↔
    ∃ x ∈ R.normalizedValues t,
      Nat.floor x = b.val := by
  constructor
  · intro hb
    have hocc :
        b ∈ occupiedCutProjectiveBands hp t c n i := by
      rw [← cutProjectiveBandPartition_active_eq_occupied
        hp hcap ht hlam hc0 hcpi n htop i]
      exact hb
    obtain ⟨j, hjBand⟩ :=
      (mem_occupiedCutProjectiveBands hp t c n i b).1 hocc
    let x := cutNormalizedRayTheta hp t c i j
    have hxMem : x ∈ R.normalizedValues t := by
      unfold CentreCutRayCycle.normalizedValues
      exact List.mem_map.mpr ⟨j, R.mem_rays j, rfl⟩
    have hx0 : 0 ≤ x :=
      cutNormalizedRayTheta_nonneg hp ht.le hc0 hcpi i j
    have hfloor : Nat.floor x = b.val := by
      apply (Nat.floor_eq_iff hx0).2
      simpa [x, RayInCutProjectiveBand] using hjBand
    exact ⟨x, hxMem, hfloor⟩
  · intro hb
    exact R.active_of_normalizedValue_floor
      hp hcap ht hlam hc0 hcpi n htop b hb

#print axioms active_iff_exists_normalizedValue_floor

end JSP000404Research
