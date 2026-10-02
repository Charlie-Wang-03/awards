import JSP000404Research.TopExponentMultiplicity
import JSP000404Research.TopTwoTailMultiplicity
import JSP000404Research.ProjectionEnlargedCandidateHallGraphFree
import Mathlib.Tactic

/-!
# Two projected-loss vertices force a second-layer or deep loss

In the planar lower branch every exponent is < n, and the top exponent n-1
occurs at most once as soon as the ambient configuration has at least three
points.

Hence two distinct projected-loss vertices cannot both be top-layer.  If one
lies below n-2, it is already a deep-loss outlet.  Otherwise one of the pair
has exponent exactly n-2.

This converts the last pair-valued hard branch of the graph-free Hall root
into a single second-layer loss centre or a standard deep-loss outlet.
-/

namespace JSP000404Research
namespace ProjectionOrdered

open OrderedEdgeColoring
open DirectionData

theorem planar_twoLoss_secondLayer_or_deep
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
      ∃ w : ProjectionOrdered V,
        w ∈ projectedLossVertices
          (planarStandardResidualColoring
            hp hcap (by omega : 1 ≤ n)
            hdelta0 (by linarith : delta < 1) ht hlam)
          (planarCentreExponent hp C)
        ∧
        centreExponent (C w) t = n - 2
    )
    ∨
    (
      ∃ w : ProjectionOrdered V,
        w ∈ projectedLossVertices
          (planarStandardResidualColoring
            hp hcap (by omega : 1 ≤ n)
            hdelta0 (by linarith : delta < 1) ht hlam)
          (planarCentreExponent hp C)
        ∧
        centreExponent (C w) t + 3 ≤ n
    ) := by
  letI : LinearOrder (ProjectionOrdered V) :=
    projectionLinearOrder hp
  have hdelta1 : delta < 1 := by linarith
  have haLt :
      centreExponent (C a) t < n :=
    centreExponent_lt_n
      (C a) n delta t (by omega : 1 ≤ n)
      hdelta0 hdelta1 ht
  have hbLt :
      centreExponent (C b) t < n :=
    centreExponent_lt_n
      (C b) n delta t (by omega : 1 ≤ n)
      hdelta0 hdelta1 ht

  by_cases haDeep : centreExponent (C a) t + 3 ≤ n
  · exact Or.inr ⟨a,haLoss,haDeep⟩
  · by_cases hbDeep : centreExponent (C b) t + 3 ≤ n
    · exact Or.inr ⟨b,hbLoss,hbDeep⟩
    · have haCases :
          centreExponent (C a) t = n - 2 ∨
          centreExponent (C a) t = n - 1 := by
        omega
      have hbCases :
          centreExponent (C b) t = n - 2 ∨
          centreExponent (C b) t = n - 1 := by
        omega
      rcases haCases with haSecond | haTop
      · exact Or.inl ⟨a,haLoss,haSecond⟩
      · rcases hbCases with hbSecond | hbTop
        · exact Or.inl ⟨b,hbLoss,hbSecond⟩
        · have htop :
            ((Finset.univ : Finset (ProjectionOrdered V)).filter
              (fun i => centreExponent (C i) t = n - 1)).card ≤ 1 := by
            exact topExponent_filter_card_le_one
              (reindexedPoint_injective hp)
              (by
                intro i j k hij hik hjk
                exact hcap
                  i.toOriginal j.toOriginal k.toOriginal
                  (by
                    intro h
                    exact hij
                      (ProjectionOrdered.toOriginal_injective h))
                  (by
                    intro h
                    exact hik
                      (ProjectionOrdered.toOriginal_injective h))
                  (by
                    intro h
                    exact hjk
                      (ProjectionOrdered.toOriginal_injective h)))
              hcard
              (by omega : 2 ≤ n)
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
        have hcardPair := Finset.card_le_card hsub
        have hp : ({a,b} : Finset (ProjectionOrdered V)).card = 2 := by
          simp [hab]
        rw [hp] at hcardPair
        omega

#print axioms planar_twoLoss_secondLayer_or_deep

end ProjectionOrdered
end JSP000404Research
