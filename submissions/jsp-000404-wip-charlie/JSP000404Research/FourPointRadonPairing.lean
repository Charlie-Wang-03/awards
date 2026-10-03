import JSP000404Research.SharpCentre
import Mathlib.Analysis.Convex.Radon
import Mathlib.Analysis.Convex.Hull
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
import Mathlib.Tactic

/-!
# Radon pairing for four strictly convex planar points

Four planar points are affinely dependent.  Radon's theorem therefore gives a
partition whose two convex hulls meet.  If no point lies in the convex hull of
the other three, the partition cannot have type 1+3.  Hence it has type 2+2.

Equivalently, one of the three pairings of the four points has intersecting
segments.  For a strictly convex four-point set this is the diagonal pairing.
-/

namespace JSP000404Research

theorem four_convex_position_has_crossing_pairing
    {a b c d : Plane}
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d)
    (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d)
    (ha : a ∉ convexHull ℝ ({b,c,d} : Set Plane))
    (hb : b ∉ convexHull ℝ ({a,c,d} : Set Plane))
    (hc : c ∉ convexHull ℝ ({a,b,d} : Set Plane))
    (hd : d ∉ convexHull ℝ ({a,b,c} : Set Plane)) :
    ((segment ℝ a b ∩ segment ℝ c d).Nonempty)
    ∨ ((segment ℝ a c ∩ segment ℝ b d).Nonempty)
    ∨ ((segment ℝ a d ∩ segment ℝ b c).Nonempty) := by
  let f : Fin 4 → Plane := ![a,b,c,d]
  have hspan :
      Module.finrank ℝ
          ↥(vectorSpan ℝ (Set.range f)) ≤ 2 := by
    calc
      Module.finrank ℝ ↥(vectorSpan ℝ (Set.range f))
          ≤ Module.finrank ℝ Plane :=
        Submodule.finrank_le _
      _ = 2 := by
        exact finrank_euclideanSpace_fin
  have hdep : ¬ AffineIndependent ℝ f := by
    exact
      (finrank_vectorSpan_le_iff_not_affineIndependent
        ℝ f (n := 2) (by simp)).1 hspan
  obtain ⟨I,hI⟩ := Convex.radon_partition hdep

  by_cases h0 : (0 : Fin 4) ∈ I <;>
  by_cases h1 : (1 : Fin 4) ∈ I <;>
  by_cases h2 : (2 : Fin 4) ∈ I <;>
  by_cases h3 : (3 : Fin 4) ∈ I
  all_goals
    have hIeq : I =
        {x : Fin 4 |
          (x = 0 ∧ (0 : Fin 4) ∈ I) ∨
          (x = 1 ∧ (1 : Fin 4) ∈ I) ∨
          (x = 2 ∧ (2 : Fin 4) ∈ I) ∨
          (x = 3 ∧ (3 : Fin 4) ∈ I)} := by
      ext x
      fin_cases x <;> simp_all
    rw [hIeq] at hI
    simp [f, convexHull_pair] at hI ⊢
  all_goals
    try { exact False.elim (ha hI) }
  all_goals
    try { exact False.elim (hb hI) }
  all_goals
    try { exact False.elim (hc hI) }
  all_goals
    try { exact False.elim (hd hI) }
  all_goals
    aesop

#print axioms four_convex_position_has_crossing_pairing

end JSP000404Research
