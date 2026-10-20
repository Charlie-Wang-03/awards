import JSP000404Research.FourPlanarRadonDependence
import JSP000404Research.StrictExposureConvexHull
import Mathlib.Analysis.Convex.Hull
import Mathlib.Tactic

/-!
# Extract a genuinely crossing pair of diagonals from four planar extreme points

Radon's theorem supplies a partition with intersecting convex hulls.
Convex hull exclusions rule out 1+3 (or 3+1) partitions, and empty
hulls rule out 0+4 or 4+0. Exhausting membership of four Fin4 labels
gives a 2+2 partition and one of the three actual crossing pairings.
No further geometric assumptions or admitted axioms.
-/

namespace JSP000404Research

theorem four_planar_hull_exclusions_force_crossing
    (p : Fin 4 → Plane)
    (hEx0 : p 0 ∉ convexHull ℝ ({p 1,p 2,p 3} : Set Plane))
    (hEx1 : p 1 ∉ convexHull ℝ ({p 0,p 2,p 3} : Set Plane))
    (hEx2 : p 2 ∉ convexHull ℝ ({p 0,p 1,p 3} : Set Plane))
    (hEx3 : p 3 ∉ convexHull ℝ ({p 0,p 1,p 2} : Set Plane)) :
    (segment ℝ (p 0) (p 1) ∩ segment ℝ (p 2) (p 3)).Nonempty ∨
    (segment ℝ (p 0) (p 2) ∩ segment ℝ (p 1) (p 3)).Nonempty ∨
    (segment ℝ (p 0) (p 3) ∩ segment ℝ (p 1) (p 2)).Nonempty := by
  classical
  obtain ⟨I, hRadon⟩ := four_planar_radon_partition p
  by_cases h0 : (0 : Fin 4) ∈ I
  ·
    by_cases h1 : (1 : Fin 4) ∈ I
    ·
      by_cases h2 : (2 : Fin 4) ∈ I
      ·
        by_cases h3 : (3 : Fin 4) ∈ I
        ·
          have hIset : I = ({0,1,2,3} : Set (Fin 4)) := by
            ext v
            fin_cases v <;> simp_all
          have hComp : Iᶜ = (∅ : Set (Fin 4)) := by
            rw [hIset]
            ext v
            fin_cases v <;> decide
          rcases hRadon with ⟨x, hxI, hxNotI⟩
          rw [hComp] at hxNotI
          have he : x ∈ (convexHull ℝ (∅ : Set Plane)) := by
            simpa [hIset, hComp] using hxNotI
          simp at he
        ·
          have hIset : I = ({0,1,2} : Set (Fin 4)) := by
            ext v
            fin_cases v <;> simp_all
          have hComp : Iᶜ = ({3} : Set (Fin 4)) := by
            rw [hIset]
            ext v
            fin_cases v <;> decide
          rcases hRadon with ⟨x, hxI, hxNotI⟩
          rw [hComp] at hxNotI
          have hsingle : x = p 3 := by
            simpa [hIset, hComp] using hxNotI
          have hrest : x ∈ convexHull ℝ ({p 0,p 1,p 2} : Set Plane) := by
            simpa [hIset, hComp] using hxI
          exact False.elim (hEx3 (hsingle ▸ hrest))
      ·
        by_cases h3 : (3 : Fin 4) ∈ I
        ·
          have hIset : I = ({0,1,3} : Set (Fin 4)) := by
            ext v
            fin_cases v <;> simp_all
          have hComp : Iᶜ = ({2} : Set (Fin 4)) := by
            rw [hIset]
            ext v
            fin_cases v <;> decide
          rcases hRadon with ⟨x, hxI, hxNotI⟩
          rw [hComp] at hxNotI
          have hsingle : x = p 2 := by
            simpa [hIset, hComp] using hxNotI
          have hrest : x ∈ convexHull ℝ ({p 0,p 1,p 3} : Set Plane) := by
            simpa [hIset, hComp] using hxI
          exact False.elim (hEx2 (hsingle ▸ hrest))
        ·
          have hIset : I = ({0,1} : Set (Fin 4)) := by
            ext v
            fin_cases v <;> simp_all
          have hComp : Iᶜ = ({2,3} : Set (Fin 4)) := by
            rw [hIset]
            ext v
            fin_cases v <;> decide
          rcases hRadon with ⟨x, hxI, hxNotI⟩
          rw [hComp] at hxNotI
          have hleft : x ∈ segment ℝ (p 0) (p 1) := by
            simpa [hIset, hComp, convexHull_pair] using hxI
          have hright : x ∈ segment ℝ (p 2) (p 3) := by
            simpa [hIset, hComp, convexHull_pair] using hxNotI
          exact Or.inl ⟨x, hleft, hright⟩
    ·
      by_cases h2 : (2 : Fin 4) ∈ I
      ·
        by_cases h3 : (3 : Fin 4) ∈ I
        ·
          have hIset : I = ({0,2,3} : Set (Fin 4)) := by
            ext v
            fin_cases v <;> simp_all
          have hComp : Iᶜ = ({1} : Set (Fin 4)) := by
            rw [hIset]
            ext v
            fin_cases v <;> decide
          rcases hRadon with ⟨x, hxI, hxNotI⟩
          rw [hComp] at hxNotI
          have hsingle : x = p 1 := by
            simpa [hIset, hComp] using hxNotI
          have hrest : x ∈ convexHull ℝ ({p 0,p 2,p 3} : Set Plane) := by
            simpa [hIset, hComp] using hxI
          exact False.elim (hEx1 (hsingle ▸ hrest))
        ·
          have hIset : I = ({0,2} : Set (Fin 4)) := by
            ext v
            fin_cases v <;> simp_all
          have hComp : Iᶜ = ({1,3} : Set (Fin 4)) := by
            rw [hIset]
            ext v
            fin_cases v <;> decide
          rcases hRadon with ⟨x, hxI, hxNotI⟩
          rw [hComp] at hxNotI
          have hleft : x ∈ segment ℝ (p 0) (p 2) := by
            simpa [hIset, hComp, convexHull_pair] using hxI
          have hright : x ∈ segment ℝ (p 1) (p 3) := by
            simpa [hIset, hComp, convexHull_pair] using hxNotI
          exact Or.inr (Or.inl ⟨x, hleft, hright⟩)
      ·
        by_cases h3 : (3 : Fin 4) ∈ I
        ·
          have hIset : I = ({0,3} : Set (Fin 4)) := by
            ext v
            fin_cases v <;> simp_all
          have hComp : Iᶜ = ({1,2} : Set (Fin 4)) := by
            rw [hIset]
            ext v
            fin_cases v <;> decide
          rcases hRadon with ⟨x, hxI, hxNotI⟩
          rw [hComp] at hxNotI
          have hleft : x ∈ segment ℝ (p 0) (p 3) := by
            simpa [hIset, hComp, convexHull_pair] using hxI
          have hright : x ∈ segment ℝ (p 1) (p 2) := by
            simpa [hIset, hComp, convexHull_pair] using hxNotI
          exact Or.inr (Or.inr ⟨x, hleft, hright⟩)
        ·
          have hIset : I = ({0} : Set (Fin 4)) := by
            ext v
            fin_cases v <;> simp_all
          have hComp : Iᶜ = ({1,2,3} : Set (Fin 4)) := by
            rw [hIset]
            ext v
            fin_cases v <;> decide
          rcases hRadon with ⟨x, hxI, hxNotI⟩
          rw [hComp] at hxNotI
          have hsingle : x = p 0 := by
            simpa [hIset, hComp] using hxI
          have hrest : x ∈ convexHull ℝ ({p 1,p 2,p 3} : Set Plane) := by
            simpa [hIset, hComp] using hxNotI
          exact False.elim (hEx0 (hsingle ▸ hrest))
  ·
    by_cases h1 : (1 : Fin 4) ∈ I
    ·
      by_cases h2 : (2 : Fin 4) ∈ I
      ·
        by_cases h3 : (3 : Fin 4) ∈ I
        ·
          have hIset : I = ({1,2,3} : Set (Fin 4)) := by
            ext v
            fin_cases v <;> simp_all
          have hComp : Iᶜ = ({0} : Set (Fin 4)) := by
            rw [hIset]
            ext v
            fin_cases v <;> decide
          rcases hRadon with ⟨x, hxI, hxNotI⟩
          rw [hComp] at hxNotI
          have hsingle : x = p 0 := by
            simpa [hIset, hComp] using hxNotI
          have hrest : x ∈ convexHull ℝ ({p 1,p 2,p 3} : Set Plane) := by
            simpa [hIset, hComp] using hxI
          exact False.elim (hEx0 (hsingle ▸ hrest))
        ·
          have hIset : I = ({1,2} : Set (Fin 4)) := by
            ext v
            fin_cases v <;> simp_all
          have hComp : Iᶜ = ({0,3} : Set (Fin 4)) := by
            rw [hIset]
            ext v
            fin_cases v <;> decide
          rcases hRadon with ⟨x, hxI, hxNotI⟩
          rw [hComp] at hxNotI
          have hleft : x ∈ segment ℝ (p 0) (p 3) := by
            simpa [hIset, hComp, convexHull_pair] using hxNotI
          have hright : x ∈ segment ℝ (p 1) (p 2) := by
            simpa [hIset, hComp, convexHull_pair] using hxI
          exact Or.inr (Or.inr ⟨x, hleft, hright⟩)
      ·
        by_cases h3 : (3 : Fin 4) ∈ I
        ·
          have hIset : I = ({1,3} : Set (Fin 4)) := by
            ext v
            fin_cases v <;> simp_all
          have hComp : Iᶜ = ({0,2} : Set (Fin 4)) := by
            rw [hIset]
            ext v
            fin_cases v <;> decide
          rcases hRadon with ⟨x, hxI, hxNotI⟩
          rw [hComp] at hxNotI
          have hleft : x ∈ segment ℝ (p 0) (p 2) := by
            simpa [hIset, hComp, convexHull_pair] using hxNotI
          have hright : x ∈ segment ℝ (p 1) (p 3) := by
            simpa [hIset, hComp, convexHull_pair] using hxI
          exact Or.inr (Or.inl ⟨x, hleft, hright⟩)
        ·
          have hIset : I = ({1} : Set (Fin 4)) := by
            ext v
            fin_cases v <;> simp_all
          have hComp : Iᶜ = ({0,2,3} : Set (Fin 4)) := by
            rw [hIset]
            ext v
            fin_cases v <;> decide
          rcases hRadon with ⟨x, hxI, hxNotI⟩
          rw [hComp] at hxNotI
          have hsingle : x = p 1 := by
            simpa [hIset, hComp] using hxI
          have hrest : x ∈ convexHull ℝ ({p 0,p 2,p 3} : Set Plane) := by
            simpa [hIset, hComp] using hxNotI
          exact False.elim (hEx1 (hsingle ▸ hrest))
    ·
      by_cases h2 : (2 : Fin 4) ∈ I
      ·
        by_cases h3 : (3 : Fin 4) ∈ I
        ·
          have hIset : I = ({2,3} : Set (Fin 4)) := by
            ext v
            fin_cases v <;> simp_all
          have hComp : Iᶜ = ({0,1} : Set (Fin 4)) := by
            rw [hIset]
            ext v
            fin_cases v <;> decide
          rcases hRadon with ⟨x, hxI, hxNotI⟩
          rw [hComp] at hxNotI
          have hleft : x ∈ segment ℝ (p 0) (p 1) := by
            simpa [hIset, hComp, convexHull_pair] using hxNotI
          have hright : x ∈ segment ℝ (p 2) (p 3) := by
            simpa [hIset, hComp, convexHull_pair] using hxI
          exact Or.inl ⟨x, hleft, hright⟩
        ·
          have hIset : I = ({2} : Set (Fin 4)) := by
            ext v
            fin_cases v <;> simp_all
          have hComp : Iᶜ = ({0,1,3} : Set (Fin 4)) := by
            rw [hIset]
            ext v
            fin_cases v <;> decide
          rcases hRadon with ⟨x, hxI, hxNotI⟩
          rw [hComp] at hxNotI
          have hsingle : x = p 2 := by
            simpa [hIset, hComp] using hxI
          have hrest : x ∈ convexHull ℝ ({p 0,p 1,p 3} : Set Plane) := by
            simpa [hIset, hComp] using hxNotI
          exact False.elim (hEx2 (hsingle ▸ hrest))
      ·
        by_cases h3 : (3 : Fin 4) ∈ I
        ·
          have hIset : I = ({3} : Set (Fin 4)) := by
            ext v
            fin_cases v <;> simp_all
          have hComp : Iᶜ = ({0,1,2} : Set (Fin 4)) := by
            rw [hIset]
            ext v
            fin_cases v <;> decide
          rcases hRadon with ⟨x, hxI, hxNotI⟩
          rw [hComp] at hxNotI
          have hsingle : x = p 3 := by
            simpa [hIset, hComp] using hxI
          have hrest : x ∈ convexHull ℝ ({p 0,p 1,p 2} : Set Plane) := by
            simpa [hIset, hComp] using hxNotI
          exact False.elim (hEx3 (hsingle ▸ hrest))
        ·
          have hIset : I = (∅ : Set (Fin 4)) := by
            ext v
            fin_cases v <;> simp_all
          have hComp : Iᶜ = ({0,1,2,3} : Set (Fin 4)) := by
            rw [hIset]
            ext v
            fin_cases v <;> decide
          rcases hRadon with ⟨x, hxI, hxNotI⟩
          rw [hComp] at hxNotI
          have he : x ∈ (convexHull ℝ (∅ : Set Plane)) := by
            simpa [hIset, hComp] using hxI
          simp at he

#print axioms four_planar_hull_exclusions_force_crossing

end JSP000404Research
