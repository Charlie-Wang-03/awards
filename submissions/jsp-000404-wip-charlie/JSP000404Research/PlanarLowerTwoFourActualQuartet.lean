import JSP000404Research.FourPlanarRadonCrossingExtraction
import JSP000404Research.PlanarLowerTwoFourSharpCrossingObstruction
import JSP000404Research.StrictExposureConvexHull
import Mathlib.Data.Matrix.Notation
import Mathlib.Tactic

/-!
# Actual four-original-centre sharp exclusion, without Fin4 cycle transport

Select any four distinct labels s,u,v,w in an arbitrary finite,
linearly ordered genuine AngleCap configuration at t=2+delta.
At n=2 every centre is strictly exposed. Map the four concrete
*points* to Fin4 for Radon pairing, but keep all centre cycles and
exponents on the ORIGINAL finite vertex type. Each of the three
crossing pairings then contradicts sharpness at s.

This theorem makes no arbitrary-cardinality Boolean payment claim.
-/

namespace JSP000404Research

theorem lower_two_no_sharp_with_three_other_centres
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane}
    (hp : Function.Injective p)
    {lam t delta : ℝ}
    (hcap : AngleCap p lam)
    (hdelta0 : 0 ≤ delta)
    (hdeltaHalf : delta < (1 : ℝ) / 2)
    (ht : t = (2 : ℝ) + delta)
    (hlam : lam = Real.pi / t)
    (C : ∀ i : V, CentreProjectiveCycle hp i)
    {s u v w : V}
    (hsu : s ≠ u) (hsv : s ≠ v) (hsw : s ≠ w)
    (huv : u ≠ v) (huw : u ≠ w) (hvw : v ≠ w)
    (hexp : centreExponent (C s) t = 1) :
    False := by
  have hExposure (i : V) : StrictlyExposedAt p i :=
    lower_two_all_centres_strictlyExposed
      hp hcap hdelta0 hdeltaHalf ht hlam C i
  obtain ⟨hHullS, hHullU, hHullV, hHullW⟩ :=
    four_strictlyExposed_convexHull_exclusions
      hsu hsv hsw huv huw hvw
      (hExposure s) (hExposure u) (hExposure v) (hExposure w)
  let f : Fin 4 → Plane := ![p s, p u, p v, p w]
  have hS :
      f 0 ∉ convexHull ℝ ({f 1, f 2, f 3} : Set Plane) := by
    simpa [f] using hHullS
  have hU :
      f 1 ∉ convexHull ℝ ({f 0, f 2, f 3} : Set Plane) := by
    simpa [f] using hHullU
  have hV :
      f 2 ∉ convexHull ℝ ({f 0, f 1, f 3} : Set Plane) := by
    simpa [f] using hHullV
  have hW :
      f 3 ∉ convexHull ℝ ({f 0, f 1, f 2} : Set Plane) := by
    simpa [f] using hHullW
  rcases four_planar_hull_exclusions_force_crossing f hS hU hV hW with
    h01 | h02 | h03
  · have hcross :
        (segment ℝ (p s) (p u) ∩
          segment ℝ (p v) (p w)).Nonempty := by
      simpa [f] using h01
    exact lower_two_no_sharp_of_crossing_diagonals
      (s := s) (b := v) (c := u) (d := w)
      hp hcap hdelta0 hdeltaHalf ht hlam C
      hsv hsu hsw huv.symm hvw huw hcross hexp
  · have hcross :
        (segment ℝ (p s) (p v) ∩
          segment ℝ (p u) (p w)).Nonempty := by
      simpa [f] using h02
    exact lower_two_no_sharp_of_crossing_diagonals
      (s := s) (b := u) (c := v) (d := w)
      hp hcap hdelta0 hdeltaHalf ht hlam C
      hsu hsv hsw huv huw hvw hcross hexp
  · have hcross :
        (segment ℝ (p s) (p w) ∩
          segment ℝ (p u) (p v)).Nonempty := by
      simpa [f] using h03
    exact lower_two_no_sharp_of_crossing_diagonals
      (s := s) (b := u) (c := w) (d := v)
      hp hcap hdelta0 hdeltaHalf ht hlam C
      hsu hsw hsv huw huv hvw.symm hcross hexp

#print axioms lower_two_no_sharp_with_three_other_centres

end JSP000404Research
