import JSP000404Research.SharpCentre
import Mathlib.Analysis.Convex.Radon
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Tactic

/-!
# Four labelled points in the Euclidean plane are affinely dependent

This provides the exact finite-dimensional input required by Mathlib's
Convex.radon_partition for proving that four strictly exposed points
admit a 2+2 partition whose diagonals cross. The Radon 2+2 extraction
is deliberately kept as the *next* geometric lemma and is not assumed.
-/

namespace JSP000404Research

theorem four_planar_points_not_affineIndependent
    (p : Fin 4 → Plane) :
    ¬ AffineIndependent ℝ p := by
  have hdim :
      Module.finrank ℝ
        (vectorSpan ℝ (Set.range p)) ≤ 2 := by
    calc
      Module.finrank ℝ (vectorSpan ℝ (Set.range p))
          ≤ Module.finrank ℝ Plane :=
            Submodule.finrank_le _
      _ = 2 := by
        simpa [Plane] using
          (finrank_euclideanSpace_fin (𝕜 := ℝ) (n := 2))
  exact (finrank_vectorSpan_le_iff_not_affineIndependent
    ℝ p (by decide : Fintype.card (Fin 4) = 2 + 2)).mp hdim

theorem four_planar_radon_partition
    (p : Fin 4 → Plane) :
    ∃ I : Set (Fin 4),
      (convexHull ℝ (p '' I) ∩
        convexHull ℝ (p '' Iᶜ)).Nonempty :=
  Convex.radon_partition
    (four_planar_points_not_affineIndependent p)

#print axioms four_planar_points_not_affineIndependent
#print axioms four_planar_radon_partition

end JSP000404Research
