import JSP000404Research.FourPlanarRadonCrossingExtraction
import JSP000404Research.PlanarLowerTwoFourSharpCrossingObstruction
import JSP000404Research.StrictExposureConvexHull
import Mathlib.Tactic

/-!
# Original Fin4: n=2 all four centres have zero dyadic exponent

Genuine AngleCap + each actual centre cycle implies every vertex is
strictly exposed (no independent convex-position hypothesis).
Finite four-point Radon + strict exposures produces a crossing pairing.
For any proposed exponent-one centre, each matching can be oriented with
that point as an endpoint of the first diagonal; the already proved
sharp-vs-quadrilateral-angle bound gives False.

This is a geometric fact, not a six-source Boolean-hole payment.
-/

namespace JSP000404Research

theorem lower_two_four_no_sharp_fin_four
    {p : Fin 4 → Plane}
    (hp : Function.Injective p)
    {lam t delta : ℝ}
    (hcap : AngleCap p lam)
    (hdelta0 : 0 ≤ delta)
    (hdeltaHalf : delta < (1 : ℝ) / 2)
    (ht : t = (2 : ℝ) + delta)
    (hlam : lam = Real.pi / t)
    (C : ∀ i : Fin 4, CentreProjectiveCycle hp i) :
    ∀ i : Fin 4, centreExponent (C i) t ≠ 1 := by
  have hEx (i : Fin 4) : StrictlyExposedAt p i :=
    lower_two_all_centres_strictlyExposed
      hp hcap hdelta0 hdeltaHalf ht hlam C i
  obtain ⟨hull0, hull1, hull2, hull3⟩ :=
    four_strictlyExposed_convexHull_exclusions
      (a := (0 : Fin 4)) (b := (1 : Fin 4))
      (c := (2 : Fin 4)) (d := (3 : Fin 4))
      (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide)
      (hEx 0) (hEx 1) (hEx 2) (hEx 3)
  have hCross := four_planar_hull_exclusions_force_crossing
    p hull0 hull1 hull2 hull3
  intro i hexp
  rcases hCross with hc0 | hc1 | hc2
  · fin_cases i
    · have hc : (segment ℝ (p 0) (p 1) ∩ segment ℝ (p 2) (p 3)).Nonempty := by
        simpa only [segment_symm, Set.inter_comm] using hc0
      exact lower_two_no_sharp_of_crossing_diagonals
        (s := (0 : Fin 4)) (b := (2 : Fin 4))
        (c := (1 : Fin 4)) (d := (3 : Fin 4))
        hp hcap hdelta0 hdeltaHalf ht hlam C
        (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) hc hexp
    · have hc : (segment ℝ (p 1) (p 0) ∩ segment ℝ (p 2) (p 3)).Nonempty := by
        simpa only [segment_symm, Set.inter_comm] using hc0
      exact lower_two_no_sharp_of_crossing_diagonals
        (s := (1 : Fin 4)) (b := (2 : Fin 4))
        (c := (0 : Fin 4)) (d := (3 : Fin 4))
        hp hcap hdelta0 hdeltaHalf ht hlam C
        (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) hc hexp
    · have hc : (segment ℝ (p 2) (p 3) ∩ segment ℝ (p 0) (p 1)).Nonempty := by
        simpa only [segment_symm, Set.inter_comm] using hc0
      exact lower_two_no_sharp_of_crossing_diagonals
        (s := (2 : Fin 4)) (b := (0 : Fin 4))
        (c := (3 : Fin 4)) (d := (1 : Fin 4))
        hp hcap hdelta0 hdeltaHalf ht hlam C
        (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) hc hexp
    · have hc : (segment ℝ (p 3) (p 2) ∩ segment ℝ (p 0) (p 1)).Nonempty := by
        simpa only [segment_symm, Set.inter_comm] using hc0
      exact lower_two_no_sharp_of_crossing_diagonals
        (s := (3 : Fin 4)) (b := (0 : Fin 4))
        (c := (2 : Fin 4)) (d := (1 : Fin 4))
        hp hcap hdelta0 hdeltaHalf ht hlam C
        (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) hc hexp
  · fin_cases i
    · have hc : (segment ℝ (p 0) (p 2) ∩ segment ℝ (p 1) (p 3)).Nonempty := by
        simpa only [segment_symm, Set.inter_comm] using hc1
      exact lower_two_no_sharp_of_crossing_diagonals
        (s := (0 : Fin 4)) (b := (1 : Fin 4))
        (c := (2 : Fin 4)) (d := (3 : Fin 4))
        hp hcap hdelta0 hdeltaHalf ht hlam C
        (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) hc hexp
    · have hc : (segment ℝ (p 1) (p 3) ∩ segment ℝ (p 0) (p 2)).Nonempty := by
        simpa only [segment_symm, Set.inter_comm] using hc1
      exact lower_two_no_sharp_of_crossing_diagonals
        (s := (1 : Fin 4)) (b := (0 : Fin 4))
        (c := (3 : Fin 4)) (d := (2 : Fin 4))
        hp hcap hdelta0 hdeltaHalf ht hlam C
        (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) hc hexp
    · have hc : (segment ℝ (p 2) (p 0) ∩ segment ℝ (p 1) (p 3)).Nonempty := by
        simpa only [segment_symm, Set.inter_comm] using hc1
      exact lower_two_no_sharp_of_crossing_diagonals
        (s := (2 : Fin 4)) (b := (1 : Fin 4))
        (c := (0 : Fin 4)) (d := (3 : Fin 4))
        hp hcap hdelta0 hdeltaHalf ht hlam C
        (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) hc hexp
    · have hc : (segment ℝ (p 3) (p 1) ∩ segment ℝ (p 0) (p 2)).Nonempty := by
        simpa only [segment_symm, Set.inter_comm] using hc1
      exact lower_two_no_sharp_of_crossing_diagonals
        (s := (3 : Fin 4)) (b := (0 : Fin 4))
        (c := (1 : Fin 4)) (d := (2 : Fin 4))
        hp hcap hdelta0 hdeltaHalf ht hlam C
        (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) hc hexp
  · fin_cases i
    · have hc : (segment ℝ (p 0) (p 3) ∩ segment ℝ (p 1) (p 2)).Nonempty := by
        simpa only [segment_symm, Set.inter_comm] using hc2
      exact lower_two_no_sharp_of_crossing_diagonals
        (s := (0 : Fin 4)) (b := (1 : Fin 4))
        (c := (3 : Fin 4)) (d := (2 : Fin 4))
        hp hcap hdelta0 hdeltaHalf ht hlam C
        (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) hc hexp
    · have hc : (segment ℝ (p 1) (p 2) ∩ segment ℝ (p 0) (p 3)).Nonempty := by
        simpa only [segment_symm, Set.inter_comm] using hc2
      exact lower_two_no_sharp_of_crossing_diagonals
        (s := (1 : Fin 4)) (b := (0 : Fin 4))
        (c := (2 : Fin 4)) (d := (3 : Fin 4))
        hp hcap hdelta0 hdeltaHalf ht hlam C
        (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) hc hexp
    · have hc : (segment ℝ (p 2) (p 1) ∩ segment ℝ (p 0) (p 3)).Nonempty := by
        simpa only [segment_symm, Set.inter_comm] using hc2
      exact lower_two_no_sharp_of_crossing_diagonals
        (s := (2 : Fin 4)) (b := (0 : Fin 4))
        (c := (1 : Fin 4)) (d := (3 : Fin 4))
        hp hcap hdelta0 hdeltaHalf ht hlam C
        (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) hc hexp
    · have hc : (segment ℝ (p 3) (p 0) ∩ segment ℝ (p 1) (p 2)).Nonempty := by
        simpa only [segment_symm, Set.inter_comm] using hc2
      exact lower_two_no_sharp_of_crossing_diagonals
        (s := (3 : Fin 4)) (b := (1 : Fin 4))
        (c := (0 : Fin 4)) (d := (2 : Fin 4))
        hp hcap hdelta0 hdeltaHalf ht hlam C
        (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) hc hexp

#print axioms lower_two_four_no_sharp_fin_four

end JSP000404Research
