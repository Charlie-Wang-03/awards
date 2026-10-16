import JSP000404Research.ProjectionEnlargedCandidateHallTriangleRefined
import JSP000404Research.ResidualTwoLeafStandardOutlet
import Mathlib.Tactic

/-!
# Graph-free planar minimal enlarged Hall root

The triangle branch has already been eliminated by
`planar_minimal_enlarged_leaf_or_twoLoss_or_recursive`.

The remaining raw graph branch consists of two distinct leaf outlets.
Each leaf outlet remembers whether its leaf is strict, exact, or projected
loss.  Hence two leaves immediately reduce to paid surplus, exact projected
budget, or a concrete pair of projected-loss vertices.

After this composition no graph-shaped terminal remains.
-/

namespace JSP000404Research
namespace ProjectionOrdered

open OrderedEdgeColoring
open DirectionData

theorem planar_minimal_enlarged_twoLoss_or_recursive
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
    {T : Finset (ProjectionOrdered V)}
    (hdef :
      BlockDeficient
        (fun i => 2 ^ centreExponent (C i) t)
        (planarEnlargedCandidateBlock
          hp hcap (by omega : 1 ≤ n)
          hdelta0 hdeltaHalf ht hlam C)
        T)
    (hmin :
      ∀ U : Finset (ProjectionOrdered V),
        U ⊂ T →
        ¬ BlockDeficient
          (fun i => 2 ^ centreExponent (C i) t)
          (planarEnlargedCandidateBlock
            hp hcap (by omega : 1 ≤ n)
            hdelta0 hdeltaHalf ht hlam C)
          U) :
    let R :=
      planarStandardResidualColoring
        hp hcap (by omega : 1 ≤ n)
        hdelta0 (by linarith : delta < 1) ht hlam
    let exponent := planarCentreExponent hp C
    (
      (
        ∃ a b : ProjectionOrdered V,
          a ∈ T ∧
          b ∈ T ∧
          a ≠ b ∧
          a ∈ projectedLossVertices R exponent ∧
          b ∈ projectedLossVertices R exponent
      )
      ∨
      (
        ∃ source : ProjectionOrdered V,
          ExactRecursiveOutlet R exponent source
      )
      ∨
      (
        ∃ hole : Fin n → Bool,
          hole ∉ coveredCompletionWords R
      )
      ∨
      (
        ∃ w : ProjectionOrdered V,
          1 ≤ dyadicProfileSurplus
            exponent (projectedFree R) w
      )
      ∨
      (
        ∃ w : ProjectionOrdered V,
          ExactProjectedBudget R exponent w
      )
      ∨
      (
        ∃ w : ProjectionOrdered V,
          w ∈ projectedLossVertices R exponent ∧
          exponent w + 3 ≤ n
      )
    ) := by
  let hn1 : 1 ≤ n := by omega
  let hdelta1 : delta < 1 := by linarith
  let R :=
    planarStandardResidualColoring
      hp hcap hn1 hdelta0 hdelta1 ht hlam
  let exponent := planarCentreExponent hp C

  rcases
    planar_minimal_enlarged_leaf_or_twoLoss_or_recursive
      hp hcap hn3 hdelta0 hdeltaHalf ht hlam
      hcard C hdef hmin
    with hleaf | hloss | hrec | hhole | hpaid | hexact | hdeep
  · obtain ⟨u,v,wu,wv,huT,hvT,huv,_hwuT,_hwvT,_hwune,_hvwne,huOut,hvOut⟩ := hleaf
    rcases
      two_enlargedLeafOutlets_standard_outlet
        R exponent huT hvT huv huOut hvOut
      with hloss' | hpaid' | hexact'
    · exact Or.inl hloss'
    · exact Or.inr (Or.inr (Or.inr (Or.inl hpaid')))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hexact'))))
  · exact Or.inl hloss
  · exact Or.inr (Or.inl hrec)
  · exact Or.inr (Or.inr (Or.inl hhole))
  · exact Or.inr (Or.inr (Or.inr (Or.inl hpaid)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hexact))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hdeep))))

#print axioms planar_minimal_enlarged_twoLoss_or_recursive

end ProjectionOrdered
end JSP000404Research
