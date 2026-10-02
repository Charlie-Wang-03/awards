import JSP000404Research.ProjectionEnlargedCandidateHallGraphFree
import JSP000404Research.ProjectionTwoLossSharpLayerSplit
import JSP000404Research.ProjectionTopSecondLossClosure
import Mathlib.Tactic

/-!
# Planar minimal Hall root reduced to the two-second-layer hard branch

Starting from the graph-free root:
* deep loss is already a standard outlet;
* a top+second projected-loss pair closes by the multiplicity-based
  second-layer three-exit theorem;
* therefore the only non-standard loss-pair branch left is two distinct
  second-layer projected-loss vertices in the minimal core.
-/

namespace JSP000404Research
namespace ProjectionOrdered

open OrderedEdgeColoring
open DirectionData

theorem planar_minimal_enlarged_twoSecond_or_standard
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
      ∃ a b : ProjectionOrdered V,
        a ∈ T ∧ b ∈ T ∧ a ≠ b ∧
        a ∈ projectedLossVertices R exponent ∧
        b ∈ projectedLossVertices R exponent ∧
        exponent a = n - 2 ∧ exponent b = n - 2
    )
    ∨
    (∃ source, ExactRecursiveOutlet R exponent source)
    ∨
    (∃ hole : Fin n → Bool, hole ∉ coveredCompletionWords R)
    ∨
    (∃ w, 1 ≤ dyadicProfileSurplus exponent (projectedFree R) w)
    ∨
    (∃ w, ExactProjectedBudget R exponent w)
    ∨
    (∃ w, w ∈ projectedLossVertices R exponent ∧ exponent w + 3 ≤ n) := by
  let hn1 : 1 ≤ n := by omega
  let hdelta1 : delta < 1 := by linarith
  let R := planarStandardResidualColoring
    hp hcap hn1 hdelta0 hdelta1 ht hlam
  let exponent := planarCentreExponent hp C

  rcases planar_minimal_enlarged_twoLoss_or_recursive
      hp hcap hn3 hdelta0 hdeltaHalf ht hlam hcard C hdef hmin
    with hloss | hrec | hhole | hpaid | hexact | hdeep
  · obtain ⟨a,b,haT,hbT,hab,haLoss,hbLoss⟩ := hloss
    rcases planar_twoLoss_twoSecond_or_topSecond_or_deep
        hp hcap hn3 hdelta0 hdeltaHalf ht hlam hcard C
        hab
        (by simpa [R,exponent] using haLoss)
        (by simpa [R,exponent] using hbLoss)
      with htwoSecond | htopSecond | hdeepPair
    · exact Or.inl
        ⟨a,b,haT,hbT,hab,haLoss,hbLoss,
          by simpa [exponent] using htwoSecond.1,
          by simpa [exponent] using htwoSecond.2⟩
    · rcases htopSecond with hAB | hBA
      · have hout := planar_topSecond_loss_pair_standard_outlet
          hp hcap hn3 hdelta0 hdeltaHalf ht hlam hcard C
          hAB.1 hAB.2
          (by simpa [R,exponent] using hbLoss)
        rcases hout with h | h | h | h
        · exact Or.inr (Or.inr (Or.inl h))
        · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
        · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))
        · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))
      · have hout := planar_topSecond_loss_pair_standard_outlet
          hp hcap hn3 hdelta0 hdeltaHalf ht hlam hcard C
          hBA.1 hBA.2
          (by simpa [R,exponent] using haLoss)
        rcases hout with h | h | h | h
        · exact Or.inr (Or.inr (Or.inl h))
        · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
        · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))
        · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))
    · rcases hdeepPair with haDeep | hbDeep
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
          ⟨a,haLoss,by simpa [exponent] using haDeep⟩))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
          ⟨b,hbLoss,by simpa [exponent] using hbDeep⟩))))
  · exact Or.inr (Or.inl hrec)
  · exact Or.inr (Or.inr (Or.inl hhole))
  · exact Or.inr (Or.inr (Or.inr (Or.inl hpaid)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hexact))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hdeep))))

#print axioms planar_minimal_enlarged_twoSecond_or_standard

end ProjectionOrdered
end JSP000404Research
