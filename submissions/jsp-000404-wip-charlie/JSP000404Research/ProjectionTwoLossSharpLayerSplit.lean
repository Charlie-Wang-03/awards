import JSP000404Research.TopExponentMultiplicity
import Mathlib.Tactic

/-!
# Sharp layer split for a pair of projected-loss vertices

For two distinct projected-loss vertices in the planar lower branch, either
one is already deep (exponent+3<=n), or both lie in the top two layers.
The top layer n-1 has multiplicity at most one, so the non-deep branch is
exactly:

* two second-layer vertices; or
* one top-layer vertex and one second-layer vertex.
-/

namespace JSP000404Research
namespace ProjectionOrdered

open OrderedEdgeColoring
open DirectionData

theorem planar_twoLoss_twoSecond_or_topSecond_or_deep
    {V : Type*} [Fintype V]
    {p : V → Plane}
    (hp : Function.Injective p)
    {lam t delta : ℝ} {n : ℕ}
    (hcap : AngleCap p lam)
    (hn3 : 3 ≤ n)
    (hdelta0 : 0 ≤ delta)
    (hdeltaHalf : delta < (1 : ℝ) / 2)
    (ht : t = (n : ℝ) + delta)
    (hlam : lam = Real.pi / t)
    (hcard : 3 ≤ Fintype.card (ProjectionOrdered V))
    (C :
      ∀ i : ProjectionOrdered V,
        CentreProjectiveCycle (reindexedPoint_injective hp) i)
    {a b : ProjectionOrdered V}
    (hab : a ≠ b)
    (haLoss :
      a ∈ projectedLossVertices
        (planarStandardResidualColoring
          hp hcap (by omega : 1 ≤ n)
          hdelta0 (by linarith : delta < 1) ht hlam)
        (planarCentreExponent hp C))
    (hbLoss :
      b ∈ projectedLossVertices
        (planarStandardResidualColoring
          hp hcap (by omega : 1 ≤ n)
          hdelta0 (by linarith : delta < 1) ht hlam)
        (planarCentreExponent hp C)) :
    (
      centreExponent (C a) t = n - 2 ∧
      centreExponent (C b) t = n - 2
    )
    ∨
    (
      (centreExponent (C a) t = n - 1 ∧
       centreExponent (C b) t = n - 2)
      ∨
      (centreExponent (C b) t = n - 1 ∧
       centreExponent (C a) t = n - 2)
    )
    ∨
    (
      centreExponent (C a) t + 3 ≤ n
      ∨
      centreExponent (C b) t + 3 ≤ n
    ) := by
  have hdelta1 : delta < 1 := by linarith
  have haLt : centreExponent (C a) t < n :=
    centreExponent_lt_n
      (C a) n delta t (by omega : 1 ≤ n)
      hdelta0 hdelta1 ht
  have hbLt : centreExponent (C b) t < n :=
    centreExponent_lt_n
      (C b) n delta t (by omega : 1 ≤ n)
      hdelta0 hdelta1 ht
  by_cases haDeep : centreExponent (C a) t + 3 ≤ n
  · exact Or.inr (Or.inr (Or.inl haDeep))
  · by_cases hbDeep : centreExponent (C b) t + 3 ≤ n
    · exact Or.inr (Or.inr (Or.inr hbDeep))
    · have haCase :
          centreExponent (C a) t = n - 2 ∨
          centreExponent (C a) t = n - 1 := by omega
      have hbCase :
          centreExponent (C b) t = n - 2 ∨
          centreExponent (C b) t = n - 1 := by omega
      rcases haCase with haSecond | haTop <;>
        rcases hbCase with hbSecond | hbTop
      · exact Or.inl ⟨haSecond,hbSecond⟩
      · exact Or.inr (Or.inl (Or.inr ⟨hbTop,haSecond⟩))
      · exact Or.inr (Or.inl (Or.inl ⟨haTop,hbSecond⟩))
      · have htop :
            ((Finset.univ : Finset (ProjectionOrdered V)).filter
              (fun i => centreExponent (C i) t = n - 1)).card ≤ 1 := by
          exact topExponent_filter_card_le_one
            (reindexedPoint_injective hp)
            (by
              intro i j k hij hik hjk
              exact hcap
                i.toOriginal j.toOriginal k.toOriginal
                (by intro h; exact hij
                  (ProjectionOrdered.toOriginal_injective h))
                (by intro h; exact hik
                  (ProjectionOrdered.toOriginal_injective h))
                (by intro h; exact hjk
                  (ProjectionOrdered.toOriginal_injective h)))
            hcard (by omega : 2 ≤ n)
            hdelta0 hdeltaHalf ht hlam C
        have hsub :
            ({a,b} : Finset (ProjectionOrdered V)) ⊆
              (Finset.univ : Finset (ProjectionOrdered V)).filter
                (fun i => centreExponent (C i) t = n - 1) := by
          intro x hx
          simp only [Finset.mem_insert, Finset.mem_singleton] at hx
          rcases hx with rfl | rfl
          · simp [haTop]
          · simp [hbTop]
        have hc := Finset.card_le_card hsub
        have hp : ({a,b} : Finset (ProjectionOrdered V)).card = 2 := by
          simp [hab]
        rw [hp] at hc
        omega

#print axioms planar_twoLoss_twoSecond_or_topSecond_or_deep

end ProjectionOrdered
end JSP000404Research
