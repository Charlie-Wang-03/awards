import JSP000404Research.ProjectionEnlargedCandidateHall
import JSP000404Research.ResidualEnlargedTriangleOutlet
import Mathlib.Tactic

/-!
# Refined planar minimal-core root with triangle elimination

The raw triangle branch is consumed immediately by the stronger triangle
classifier, leaving only a concrete two-loss pair, positive surplus, or an
ExactRecursiveOutlet.  The only graph-theoretic terminal left is the
two-leaf branch.
-/

namespace JSP000404Research
namespace ProjectionOrdered

open OrderedEdgeColoring
open DirectionData

theorem planar_minimal_enlarged_leaf_or_twoLoss_or_recursive
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
        ∃ u v wu wv : ProjectionOrdered V,
          u ∈ T ∧
          v ∈ T ∧
          u ≠ v ∧
          wu ∈ T ∧
          wv ∈ T ∧
          wu ≠ u ∧
          wv ≠ v ∧
          EnlargedLeafOutlet R exponent T u wu ∧
          EnlargedLeafOutlet R exponent T v wv
      )
      ∨
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

  have hexpLt :
      ∀ x : ProjectionOrdered V, exponent x < n :=
    planarCentreExponent_lt_n
      hp hn1 hdelta0 hdelta1 ht C
  have hexp :
      ∀ x : ProjectionOrdered V, exponent x ≤ n := by
    intro x
    exact Nat.le_of_lt (hexpLt x)
  have hone :
      ∀ x, (active R x).card ≤ n - exponent x + 1 :=
    planarStandardResidual_oneLayer_budget
      hp hcap hn1 hdelta0 hdelta1 ht hlam C
  have hdefR :
      BlockDeficient
        (fun x => 2 ^ exponent x)
        (enlargedProjectedCandidateBlock R exponent)
        T := by
    simpa [planarEnlargedCandidateBlock,R,exponent,
      planarCentreExponent,hn1,hdelta1] using hdef
  have hminR :
      ∀ U : Finset (ProjectionOrdered V),
        U ⊂ T →
        ¬ BlockDeficient
          (fun x => 2 ^ exponent x)
          (enlargedProjectedCandidateBlock R exponent)
          U := by
    intro U hUT
    simpa [planarEnlargedCandidateBlock,R,exponent,
      planarCentreExponent,hn1,hdelta1] using hmin U hUT

  rcases
    minimal_enlargedCollisionGraph_leaf_outlets_or_triangle_or_long_cycle
      R exponent hexpLt hexp hone hdefR hminR
    with hleaf | htri | hlong
  · exact Or.inl hleaf
  · obtain ⟨u,v,w,huv,huw,hvw⟩ := htri
    rcases
      enlargedCollisionGraph_triangle_twoLoss_or_paid_or_exactRecursive
        R exponent hexp hone T huv huw hvw
      with hloss | hpaid | hrec
    · obtain ⟨a,b,hab,haLoss,hbLoss⟩ := hloss
      exact Or.inr (Or.inl
        ⟨a.1,b.1,a.2,b.2,
          (by
            intro h
            apply hab
            apply Subtype.ext
            exact h),
          haLoss,hbLoss⟩)
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hpaid))))
    · exact Or.inr (Or.inr (Or.inl hrec))
  · rcases
      planar_longCycle_overload_recursive_outlet
        hp hcap hn3 hdelta0 hdeltaHalf ht hlam
        hcard C
        (T := T)
        (by simpa [R,exponent,hn1,hdelta1] using hdefR)
        (by simpa [R,exponent,hn1,hdelta1] using hlong)
      with hexactRec | hhole | hpaid | hexact | hdeep
    · obtain ⟨v,_hvT,hout⟩ := hexactRec
      exact Or.inr (Or.inr (Or.inl ⟨v,hout⟩))
    · exact Or.inr (Or.inr (Or.inr (Or.inl hhole)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hpaid))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hexact)))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hdeep))))

#print axioms planar_minimal_enlarged_leaf_or_twoLoss_or_recursive

end ProjectionOrdered
end JSP000404Research
