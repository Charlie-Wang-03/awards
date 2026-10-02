import JSP000404Research.ProjectionTwoLossSharpLayerSplit
import JSP000404Research.ResidualLossThreeExitRecursiveOutlet
import JSP000404Research.SharpSecondLayerMultiplicity
import JSP000404Research.TopExponentMultiplicity
import JSP000404Research.ProjectionStandardBandBudget
import Mathlib.Tactic

/-!
# Close the top-plus-second projected-loss pair branch

If a projected-loss pair consists of one top centre and one second-layer
centre, the fixed top centre forces global top multiplicity at most one and
global second-layer multiplicity at most two.

Choose any completion word at the second-layer loss centre.  The existing
three-exit multiplicity outlet then closes the branch to hole, paid surplus,
exact projected budget, or deep projected loss.
-/

namespace JSP000404Research
namespace ProjectionOrdered

open OrderedEdgeColoring
open DirectionData

theorem planar_topSecond_loss_pair_standard_outlet
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
    {top second : ProjectionOrdered V}
    (htopExp : centreExponent (C top) t = n - 1)
    (hsecondExp : centreExponent (C second) t = n - 2)
    (hsecondLoss :
      second ∈ projectedLossVertices
        (planarStandardResidualColoring
          hp hcap (by omega : 1 ≤ n)
          hdelta0 (by linarith : delta < 1) ht hlam)
        (planarCentreExponent hp C)) :
    let R :=
      planarStandardResidualColoring
        hp hcap (by omega : 1 ≤ n)
        hdelta0 (by linarith : delta < 1) ht hlam
    let exponent := planarCentreExponent hp C
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
    ) := by
  letI : LinearOrder (ProjectionOrdered V) :=
    projectionLinearOrder hp
  let hn1 : 1 ≤ n := by omega
  let hdelta1 : delta < 1 := by linarith
  let R :=
    planarStandardResidualColoring
      hp hcap hn1 hdelta0 hdelta1 ht hlam
  let exponent := planarCentreExponent hp C

  have hcapR :
      AngleCap (reindexedPoint p) lam := by
    intro a b c hab hac hbc
    exact hcap
      a.toOriginal b.toOriginal c.toOriginal
      (by intro h; exact hab
        (ProjectionOrdered.toOriginal_injective h))
      (by intro h; exact hac
        (ProjectionOrdered.toOriginal_injective h))
      (by intro h; exact hbc
        (ProjectionOrdered.toOriginal_injective h))

  have hexpLt : ∀ z : ProjectionOrdered V, exponent z < n :=
    planarCentreExponent_lt_n
      hp hn1 hdelta0 hdelta1 ht C
  have hexp : ∀ z : ProjectionOrdered V, exponent z ≤ n := by
    intro z
    exact Nat.le_of_lt (hexpLt z)
  have hone :
      ∀ z, (active R z).card ≤ n - exponent z + 1 :=
    planarStandardResidual_oneLayer_budget
      hp hcap hn1 hdelta0 hdelta1 ht hlam C

  have htopCount :
      ((Finset.univ : Finset (ProjectionOrdered V)).filter
        (fun z => exponent z = n - 1)).card ≤ 1 := by
    simpa [exponent] using
      (topExponent_filter_card_le_one
        (reindexedPoint_injective hp) hcapR
        hcard (by omega : 2 ≤ n)
        hdelta0 hdeltaHalf ht hlam C)

  have hcompanion :
      ((Finset.univ : Finset (ProjectionOrdered V)).filter
        (fun z => z ≠ top ∧ exponent z = n - 2)).card ≤ 2 := by
    simpa [exponent] using
      (secondLayer_companion_card_le_two
        (reindexedPoint_injective hp) hcapR
        hn3 hdelta0 hdeltaHalf ht hlam C top htopExp)

  have hsecondCount :
      ((Finset.univ : Finset (ProjectionOrdered V)).filter
        (fun z => exponent z = n - 2)).card ≤ 2 := by
    have hEq :
        ((Finset.univ : Finset (ProjectionOrdered V)).filter
          (fun z => exponent z = n - 2))
        =
        ((Finset.univ : Finset (ProjectionOrdered V)).filter
          (fun z => z ≠ top ∧ exponent z = n - 2)) := by
      ext z
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · intro hz
        refine ⟨?_,hz⟩
        intro hzt
        subst z
        rw [htopExp] at hz
        omega
      · exact fun hz => hz.2
    rw [hEq]
    exact hcompanion

  have hsecondLoss' :
      second ∈ projectedLossVertices R exponent := by
    simpa [R,exponent] using hsecondLoss
  have hsecondExp' : exponent second = n - 2 := by
    simpa [exponent] using hsecondExp

  have hcubeNonempty :
      (retainedCompletionWords R second).Nonempty := by
    apply Finset.card_pos.mp
    rw [retainedCompletionWords_card]
    positivity
  obtain ⟨word,hword⟩ := hcubeNonempty

  rcases
    secondLayerLoss_word_closed_outlet_of_multiplicity
      R exponent hexpLt hexp hone
      htopCount hsecondCount
      hsecondLoss' hsecondExp' hword
    with hhole | hpaid | hexact | hdeep
  · exact Or.inl
      ⟨flipBoolWordAt word hhole.choose, hhole.choose_spec.2⟩
  · exact Or.inr (Or.inl hpaid)
  · exact Or.inr (Or.inr (Or.inl hexact))
  · exact Or.inr (Or.inr (Or.inr hdeep))

#print axioms planar_topSecond_loss_pair_standard_outlet

end ProjectionOrdered
end JSP000404Research
