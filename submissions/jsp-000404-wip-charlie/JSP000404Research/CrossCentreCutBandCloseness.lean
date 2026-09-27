import JSP000404Research.CutMergedCrossCentreFibre
import Mathlib.Tactic

/-!
# Cross-centre direction closeness inside one old cut band

The old cut-projective colour is a global undirected edge-direction band.
Therefore two arbitrary incident edges, possibly at different centres, with
the same old cut colour have normalized cut direction coordinates differing
by strictly less than one unit.

Under lambda = pi/t this is the numerical statement that their projective
direction parameters differ by strictly less than lambda.
-/

namespace JSP000404Research

open BinaryEdgePartition
open Real

theorem abs_sub_lt_one_of_same_cut_band_values
    {x y : ℝ} {b : ℕ}
    (hx : (b : ℝ) ≤ x)
    (hx' : x < (b : ℝ) + 1)
    (hy : (b : ℝ) ≤ y)
    (hy' : y < (b : ℝ) + 1) :
    |x - y| < 1 := by
  rw [abs_lt]
  constructor <;> linarith

theorem abs_cutNormalizedRayTheta_lt_one_of_equal_cut_color
    {V : Type*} [LinearOrder V]
    {p : V → Plane} (hp : Function.Injective p)
    {t c : ℝ}
    (ht : 0 < t)
    (hc0 : 0 ≤ c) (hcpi : c < Real.pi)
    (n : ℕ)
    (htop : t < (n + 1 : ℕ))
    {i x j y : V}
    (hix : i ≠ x)
    (hjy : j ≠ y)
    (heq :
      cutProjectiveBandColor hp ht hc0 hcpi n htop i x =
      cutProjectiveBandColor hp ht hc0 hcpi n htop j y) :
    |cutNormalizedRayTheta hp t c i ⟨x, hix.symm⟩ -
      cutNormalizedRayTheta hp t c j ⟨y, hjy.symm⟩| < 1 := by
  let bix :=
    cutProjectiveBandColor hp ht hc0 hcpi n htop i x
  let bjy :=
    cutProjectiveBandColor hp ht hc0 hcpi n htop j y
  have hb : bix = bjy := heq
  have hixBand :
      RayInCutProjectiveBand hp t c i ⟨x, hix.symm⟩ bix :=
    cutProjectiveBandColor_mem_lower
      hp ht hc0 hcpi n htop hix
  have hjyBand0 :
      RayInCutProjectiveBand hp t c j ⟨y, hjy.symm⟩ bjy :=
    cutProjectiveBandColor_mem_lower
      hp ht hc0 hcpi n htop hjy
  have hjyBand :
      RayInCutProjectiveBand hp t c j ⟨y, hjy.symm⟩ bix := by
    simpa [hb] using hjyBand0
  exact abs_sub_lt_one_of_same_cut_band_values
    hixBand.1 hixBand.2 hjyBand.1 hjyBand.2

theorem abs_cutRayTheta_lt_lam_of_equal_cut_color
    {V : Type*} [LinearOrder V]
    {p : V → Plane} (hp : Function.Injective p)
    {t lam c : ℝ}
    (ht : 0 < t)
    (hlam : lam = Real.pi / t)
    (hc0 : 0 ≤ c) (hcpi : c < Real.pi)
    (n : ℕ)
    (htop : t < (n + 1 : ℕ))
    {i x j y : V}
    (hix : i ≠ x)
    (hjy : j ≠ y)
    (heq :
      cutProjectiveBandColor hp ht hc0 hcpi n htop i x =
      cutProjectiveBandColor hp ht hc0 hcpi n htop j y) :
    |cutRayTheta hp c i ⟨x, hix.symm⟩ -
      cutRayTheta hp c j ⟨y, hjy.symm⟩| < lam := by
  have hnorm :=
    abs_cutNormalizedRayTheta_lt_one_of_equal_cut_color
      hp ht hc0 hcpi n htop hix hjy heq
  unfold cutNormalizedRayTheta at hnorm
  have hpi : 0 < Real.pi := Real.pi_pos
  have hscale : 0 < t / Real.pi := div_pos ht hpi
  have hre :
      t * cutRayTheta hp c i ⟨x, hix.symm⟩ / Real.pi -
        t * cutRayTheta hp c j ⟨y, hjy.symm⟩ / Real.pi
      =
      (t / Real.pi) *
        (cutRayTheta hp c i ⟨x, hix.symm⟩ -
         cutRayTheta hp c j ⟨y, hjy.symm⟩) := by
    ring
  rw [hre, abs_mul, abs_of_pos hscale] at hnorm
  rw [hlam]
  have hinv : Real.pi / t = 1 / (t / Real.pi) := by
    field_simp [ne_of_gt ht, Real.pi_ne_zero]
  rw [hinv]
  exact (mul_lt_one_iff_lt_inv₀ hscale).mp hnorm

#print axioms abs_sub_lt_one_of_same_cut_band_values
#print axioms abs_cutNormalizedRayTheta_lt_one_of_equal_cut_color
#print axioms abs_cutRayTheta_lt_lam_of_equal_cut_color

end JSP000404Research
