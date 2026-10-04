
import JSP000404Research.PlanarStandardResidualBudget
import JSP000404Research.PlanarStandardResidualColoring
import JSP000404Research.PlanarCentreExponent
import JSP000404Research.ResidualHardRemainder
import JSP000404Research.ResidualEnlargedCollisionSimpleGraph
import JSP000404Research.GenericTopExponentMultiplicity
import JSP000404Research.SharpSecondLayerMultiplicity
import JSP000404Research.ResidualWeightedRecursionRank
import Mathlib.Tactic

/-!
# Genuine planar reduction to the concrete residual hard-word remainder

The residual projection route is now fully connected to the actual planar
Sendov centre exponents.

For an injective finite planar configuration in the nonintegral regime

  t = n + delta,  0 <= delta < 1,

use the generic projection order and its standard (n+1)-band residual
colouring.  ProjectionCutLocalCycle identifies the local DirectionData cyclic
exponent with the genuine centreExponent, and PlanarStandardResidualBudget
proves the required one-layer active-colour estimate.

Therefore all abstract hypotheses of ResidualHardRemainder are automatic.

The only remaining Boolean projection obligation is the concrete inequality

  card(saturatedOverlapWords)
    + card(lossCompletionWords)
      <=
  2^n - card(coveredCompletionWords).

Any proof of this hard-word-to-hole payment immediately gives the sharp
centre-level dyadic capacity.
-/

namespace JSP000404Research
namespace ProjectionOrdered

open OrderedEdgeColoring
open DirectionData
open scoped BigOperators

section

variable {V : Type*} [Fintype V]
variable {p : V → Plane}
variable (hp : Function.Injective p)

local instance projectionOrder :
    LinearOrder (ProjectionOrdered V) :=
  projectionLinearOrder hp

theorem planarCentreExponent_le_n
    {t delta : ℝ} {n : ℕ}
    (hn : 1 ≤ n)
    (hdelta0 : 0 ≤ delta)
    (hdelta1 : delta < 1)
    (ht : t = (n : ℝ) + delta)
    (C : ∀ i : ProjectionOrdered V,
      CentreProjectiveCycle
        (reindexedPoint_injective hp) i) :
    ∀ i, planarCentreExponent hp C i ≤ n := by
  intro i
  unfold planarCentreExponent
  have hlt :=
    centreExponent_lt_n
      (C i) n delta t
      hn hdelta0 hdelta1 ht
  omega

theorem planarStandardResidual_oneLayer_budget
    {lam t delta : ℝ} {n : ℕ}
    (hcap : AngleCap p lam)
    (hn : 1 ≤ n)
    (hdelta0 : 0 ≤ delta)
    (hdelta1 : delta < 1)
    (ht : t = (n : ℝ) + delta)
    (hlam : lam = Real.pi / t)
    (C : ∀ i : ProjectionOrdered V,
      CentreProjectiveCycle
        (reindexedPoint_injective hp) i) :
    let R :=
      planarStandardResidualColoring
        hp hcap hn hdelta0 hdelta1 ht hlam
    ∀ i,
      (active R i).card ≤
        n - planarCentreExponent hp C i + 1 := by
  dsimp [planarStandardResidualColoring,
    planarCentreExponent]
  exact planarStandardResidual_oneLayer_family
    hp hcap hn hdelta0 hdelta1 ht hlam C


theorem planarCentreExponent_lt_n
    {t delta : ℝ} {n : ℕ}
    (hn : 1 ≤ n)
    (hdelta0 : 0 ≤ delta)
    (hdelta1 : delta < 1)
    (ht : t = (n : ℝ) + delta)
    (C : ∀ i : ProjectionOrdered V,
      CentreProjectiveCycle
        (reindexedPoint_injective hp) i) :
    ∀ i, planarCentreExponent hp C i < n := by
  intro i
  unfold planarCentreExponent
  exact centreExponent_lt_n
    (C i) n delta t hn hdelta0 hdelta1 ht

theorem planar_topLoss_word_four_exit_outlet
    {lam t delta : ℝ} {n : ℕ}
    (hcap : AngleCap p lam)
    (hcard : 3 ≤ Fintype.card (ProjectionOrdered V))
    (hn : 2 ≤ n)
    (hdelta0 : 0 ≤ delta)
    (hdeltaHalf : delta < (1 : ℝ) / 2)
    (ht : t = (n : ℝ) + delta)
    (hlam : lam = Real.pi / t)
    (C : ∀ i : ProjectionOrdered V,
      CentreProjectiveCycle
        (reindexedPoint_injective hp) i)
    {v : ProjectionOrdered V}
    (hvLoss :
      let R :=
        planarStandardResidualColoring
          hp hcap (by omega : 1 ≤ n)
          hdelta0 (by linarith : delta < 1)
          ht hlam
      let exponent := planarCentreExponent hp C
      v ∈ projectedLossVertices R exponent)
    (hvTop :
      planarCentreExponent hp C v = n - 1)
    {word : Fin n → Bool}
    (hword :
      let R :=
        planarStandardResidualColoring
          hp hcap (by omega : 1 ≤ n)
          hdelta0 (by linarith : delta < 1)
          ht hlam
      word ∈ retainedCompletionWords R v) :
    let R :=
      planarStandardResidualColoring
        hp hcap (by omega : 1 ≤ n)
        hdelta0 (by linarith : delta < 1)
        ht hlam
    let exponent := planarCentreExponent hp C
    (
      ∃ e : Fin n,
        e ∈ retainedActive R v ∧
        flipBoolWordAt word e ∉ coveredCompletionWords R
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
        exponent w + 1 ≤ n - 1
    ) := by
  let hn1 : 1 ≤ n := by omega
  let hdelta1 : delta < 1 := by linarith
  let R :=
    planarStandardResidualColoring
      hp hcap hn1 hdelta0 hdelta1 ht hlam
  let exponent := planarCentreExponent hp C
  have hvLoss' :
      v ∈ projectedLossVertices R exponent := by
    simpa [R,exponent,hn1,hdelta1] using hvLoss
  have hword' :
      word ∈ retainedCompletionWords R v := by
    simpa [R,hn1,hdelta1] using hword
  have hexpLt :
      ∀ i, exponent i < n := by
    intro i
    exact planarCentreExponent_lt_n
      hp hn1 hdelta0 hdelta1 ht C i
  have hexp :
      ∀ i, exponent i ≤ n := by
    intro i
    exact Nat.le_of_lt (hexpLt i)
  have hone :
      ∀ i, (active R i).card ≤
        n - exponent i + 1 := by
    exact planarStandardResidual_oneLayer_budget
      hp hcap hn1 hdelta0 hdelta1 ht hlam C
  have hfive :=
    topLoss_word_five_exit_outlet
      R exponent hexpLt hexp hone
      hvLoss' hvTop hword'
  rcases hfive with hhole | hpaid | hexact | hlower | htwoTop
  · exact Or.inl hhole
  · exact Or.inr (Or.inl hpaid)
  · exact Or.inr (Or.inr (Or.inl hexact))
  · exact Or.inr (Or.inr (Or.inr hlower))
  · obtain ⟨w,z,hwz,_hwLoss,_hzLoss,hwTop,hzTop⟩ := htwoTop
    have htopCard :=
      projectionOrdered_topExponent_filter_card_le_one
        hp hcap hcard hn hdelta0 hdeltaHalf
        ht hlam C
    have hwMem :
        w ∈
          (Finset.univ : Finset (ProjectionOrdered V)).filter
            (fun i => centreExponent (C i) t = n - 1) := by
      simp [exponent, planarCentreExponent] at hwTop ⊢
      exact hwTop
    have hzMem :
        z ∈
          (Finset.univ : Finset (ProjectionOrdered V)).filter
            (fun i => centreExponent (C i) t = n - 1) := by
      simp [exponent, planarCentreExponent] at hzTop ⊢
      exact hzTop
    have hwzEq :=
      Finset.card_le_one.mp htopCard
        w hwMem z hzMem
    exact False.elim (hwz hwzEq)


theorem planar_topLoss_word_layered_outlet
    {lam t delta : ℝ} {n : ℕ}
    (hcap : AngleCap p lam)
    (hcard : 3 ≤ Fintype.card (ProjectionOrdered V))
    (hn : 2 ≤ n)
    (hdelta0 : 0 ≤ delta)
    (hdeltaHalf : delta < (1 : ℝ) / 2)
    (ht : t = (n : ℝ) + delta)
    (hlam : lam = Real.pi / t)
    (C : ∀ i : ProjectionOrdered V,
      CentreProjectiveCycle
        (reindexedPoint_injective hp) i)
    {v : ProjectionOrdered V}
    (hvLoss :
      let R :=
        planarStandardResidualColoring
          hp hcap (by omega : 1 ≤ n)
          hdelta0 (by linarith : delta < 1)
          ht hlam
      let exponent := planarCentreExponent hp C
      v ∈ projectedLossVertices R exponent)
    (hvTop :
      planarCentreExponent hp C v = n - 1)
    {word : Fin n → Bool}
    (hword :
      let R :=
        planarStandardResidualColoring
          hp hcap (by omega : 1 ≤ n)
          hdelta0 (by linarith : delta < 1)
          ht hlam
      word ∈ retainedCompletionWords R v) :
    let R :=
      planarStandardResidualColoring
        hp hcap (by omega : 1 ≤ n)
        hdelta0 (by linarith : delta < 1)
        ht hlam
    let exponent := planarCentreExponent hp C
    (
      ∃ e : Fin n,
        e ∈ retainedActive R v ∧
        flipBoolWordAt word e ∉ coveredCompletionWords R
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
        exponent w = n - 2
    )
    ∨
    (
      ∃ w : ProjectionOrdered V,
        w ∈ projectedLossVertices R exponent ∧
        exponent w + 3 ≤ n
    ) := by
  let hn1 : 1 ≤ n := by omega
  let hdelta1 : delta < 1 := by linarith
  let R :=
    planarStandardResidualColoring
      hp hcap hn1 hdelta0 hdelta1 ht hlam
  let exponent := planarCentreExponent hp C
  have hfour :=
    planar_topLoss_word_four_exit_outlet
      hp hcap hcard hn hdelta0 hdeltaHalf
      ht hlam C hvLoss hvTop hword
  dsimp [R,exponent,hn1,hdelta1] at hfour ⊢
  rcases hfour with hhole | hpaid | hexact | hlower
  · exact Or.inl hhole
  · exact Or.inr (Or.inl hpaid)
  · exact Or.inr (Or.inr (Or.inl hexact))
  · obtain ⟨w,hwLoss,hwLower⟩ := hlower
    have hwLt :
        planarCentreExponent hp C w < n :=
      planarCentreExponent_lt_n
        hp hn1 hdelta0 hdelta1 ht C w
    rcases lowerLoss_secondLayer_or_deep
        R (planarCentreExponent hp C)
        hwLoss hwLt hwLower
      with hsecond | hdeep
    · exact Or.inr (Or.inr (Or.inr
        (Or.inl ⟨w,hwLoss,hsecond⟩)))
    · exact Or.inr (Or.inr (Or.inr
        (Or.inr ⟨w,hwLoss,hdeep⟩)))

theorem planar_topLoss_secondLayer_companion_card_le_two
    {lam t delta : ℝ} {n : ℕ}
    (hcap : AngleCap p lam)
    (hn : 3 ≤ n)
    (hdelta0 : 0 ≤ delta)
    (hdeltaHalf : delta < (1 : ℝ) / 2)
    (ht : t = (n : ℝ) + delta)
    (hlam : lam = Real.pi / t)
    (C : ∀ i : ProjectionOrdered V,
      CentreProjectiveCycle
        (reindexedPoint_injective hp) i)
    (s : ProjectionOrdered V)
    (hS : planarCentreExponent hp C s = n - 1) :
    ((Finset.univ : Finset (ProjectionOrdered V)).filter
      (fun i =>
        i ≠ s ∧
        planarCentreExponent hp C i = n - 2)).card ≤ 2 := by
  have hcapRe :
      AngleCap (reindexedPoint p) lam :=
    angleCap_reindexedPoint hp hcap
  exact secondLayer_companion_card_le_two
    (reindexedPoint_injective hp)
    hcapRe hn hdelta0 hdeltaHalf ht hlam
    C s hS


noncomputable def planarTopSecondLayerLossVertices
    {lam t delta : ℝ} {n : ℕ}
    (hcap : AngleCap p lam)
    (hn : 3 ≤ n)
    (hdelta0 : 0 ≤ delta)
    (hdeltaHalf : delta < (1 : ℝ) / 2)
    (ht : t = (n : ℝ) + delta)
    (hlam : lam = Real.pi / t)
    (C : ∀ i : ProjectionOrdered V,
      CentreProjectiveCycle
        (reindexedPoint_injective hp) i)
    (s : ProjectionOrdered V) :
    Finset (ProjectionOrdered V) := by
  classical
  let R :=
    planarStandardResidualColoring
      hp hcap (by omega : 1 ≤ n)
      hdelta0 (by linarith : delta < 1)
      ht hlam
  let exponent := planarCentreExponent hp C
  exact (Finset.univ : Finset (ProjectionOrdered V)).filter
    (fun i =>
      i ≠ s ∧
      i ∈ projectedLossVertices R exponent ∧
      exponent i = n - 2)

theorem planarTopSecondLayerLossVertices_card_le_two
    {lam t delta : ℝ} {n : ℕ}
    (hcap : AngleCap p lam)
    (hn : 3 ≤ n)
    (hdelta0 : 0 ≤ delta)
    (hdeltaHalf : delta < (1 : ℝ) / 2)
    (ht : t = (n : ℝ) + delta)
    (hlam : lam = Real.pi / t)
    (C : ∀ i : ProjectionOrdered V,
      CentreProjectiveCycle
        (reindexedPoint_injective hp) i)
    (s : ProjectionOrdered V)
    (hS : planarCentreExponent hp C s = n - 1) :
    (planarTopSecondLayerLossVertices
      hp hcap hn hdelta0 hdeltaHalf ht hlam C s).card ≤ 2 := by
  classical
  let S :=
    planarTopSecondLayerLossVertices
      hp hcap hn hdelta0 hdeltaHalf ht hlam C s
  let A :=
    (Finset.univ : Finset (ProjectionOrdered V)).filter
      (fun i =>
        i ≠ s ∧
        planarCentreExponent hp C i = n - 2)
  have hsub : S ⊆ A := by
    intro i hi
    simp only [S,planarTopSecondLayerLossVertices,
      Finset.mem_filter, Finset.mem_univ, true_and] at hi
    simp only [A,Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨hi.1,hi.2.2⟩
  have hcardA :
      A.card ≤ 2 := by
    simpa [A] using
      planar_topLoss_secondLayer_companion_card_le_two
        hp hcap hn hdelta0 hdeltaHalf
        ht hlam C s hS
  exact (Finset.card_le_card hsub).trans hcardA

theorem planar_secondLayerLoss_completion_card
    {lam t delta : ℝ} {n : ℕ}
    (hcap : AngleCap p lam)
    (hn : 3 ≤ n)
    (hdelta0 : 0 ≤ delta)
    (hdeltaHalf : delta < (1 : ℝ) / 2)
    (ht : t = (n : ℝ) + delta)
    (hlam : lam = Real.pi / t)
    (C : ∀ i : ProjectionOrdered V,
      CentreProjectiveCycle
        (reindexedPoint_injective hp) i)
    {w : ProjectionOrdered V}
    (hwLoss :
      let R :=
        planarStandardResidualColoring
          hp hcap (by omega : 1 ≤ n)
          hdelta0 (by linarith : delta < 1)
          ht hlam
      let exponent := planarCentreExponent hp C
      w ∈ projectedLossVertices R exponent)
    (hwSecond :
      planarCentreExponent hp C w = n - 2) :
    let R :=
      planarStandardResidualColoring
        hp hcap (by omega : 1 ≤ n)
        hdelta0 (by linarith : delta < 1)
        ht hlam
    (retainedCompletionWords R w).card = 2 ^ (n - 3) := by
  let hn1 : 1 ≤ n := by omega
  let hdelta1 : delta < 1 := by linarith
  let R :=
    planarStandardResidualColoring
      hp hcap hn1 hdelta0 hdelta1 ht hlam
  let exponent := planarCentreExponent hp C
  have hwLoss' :
      w ∈ projectedLossVertices R exponent := by
    simpa [R,exponent,hn1,hdelta1] using hwLoss
  rw [retainedCompletionWords_card]
  have heq :=
    (mem_projectedLossVertices R exponent w).1 hwLoss'
  unfold projectedFree at heq
  have hfree :
      n - (retainedActive R w).card = n - 3 := by
    rw [projectedLoss_retainedActive_card
      R exponent hwLoss']
    dsimp [exponent]
    rw [hwSecond]
    omega
  rw [hfree]

theorem planar_top_secondLayerLoss_total_cube_le_top_cube
    {lam t delta : ℝ} {n : ℕ}
    (hcap : AngleCap p lam)
    (hn : 3 ≤ n)
    (hdelta0 : 0 ≤ delta)
    (hdeltaHalf : delta < (1 : ℝ) / 2)
    (ht : t = (n : ℝ) + delta)
    (hlam : lam = Real.pi / t)
    (C : ∀ i : ProjectionOrdered V,
      CentreProjectiveCycle
        (reindexedPoint_injective hp) i)
    {s : ProjectionOrdered V}
    (hsLoss :
      let R :=
        planarStandardResidualColoring
          hp hcap (by omega : 1 ≤ n)
          hdelta0 (by linarith : delta < 1)
          ht hlam
      let exponent := planarCentreExponent hp C
      s ∈ projectedLossVertices R exponent)
    (hS : planarCentreExponent hp C s = n - 1) :
    let R :=
      planarStandardResidualColoring
        hp hcap (by omega : 1 ≤ n)
        hdelta0 (by linarith : delta < 1)
        ht hlam
    let S :=
      planarTopSecondLayerLossVertices
        hp hcap hn hdelta0 hdeltaHalf ht hlam C s
    (∑ w ∈ S, (retainedCompletionWords R w).card)
      ≤
    (retainedCompletionWords R s).card := by
  classical
  let hn1 : 1 ≤ n := by omega
  let hdelta1 : delta < 1 := by linarith
  let R :=
    planarStandardResidualColoring
      hp hcap hn1 hdelta0 hdelta1 ht hlam
  let exponent := planarCentreExponent hp C
  let S :=
    planarTopSecondLayerLossVertices
      hp hcap hn hdelta0 hdeltaHalf ht hlam C s
  have hsLoss' :
      s ∈ projectedLossVertices R exponent := by
    simpa [R,exponent,hn1,hdelta1] using hsLoss
  have hScard :
      S.card ≤ 2 :=
    planarTopSecondLayerLossVertices_card_le_two
      hp hcap hn hdelta0 hdeltaHalf ht hlam C s hS
  have hsum :
      (∑ w ∈ S, (retainedCompletionWords R w).card)
        =
      S.card * 2 ^ (n - 3) := by
    calc
      (∑ w ∈ S, (retainedCompletionWords R w).card)
          =
      ∑ _w ∈ S, 2 ^ (n - 3) := by
        apply Finset.sum_congr rfl
        intro w hwS
        have hwData :
            w ≠ s ∧
            w ∈ projectedLossVertices R exponent ∧
            exponent w = n - 2 := by
          simpa [S,planarTopSecondLayerLossVertices,
            R,exponent,hn1,hdelta1] using hwS
        exact planar_secondLayerLoss_completion_card
          hp hcap hn hdelta0 hdeltaHalf ht hlam C
          hwData.2.1 hwData.2.2
      _ = S.card * 2 ^ (n - 3) := by
        simp [Nat.mul_comm]
  have htopCard :
      (retainedCompletionWords R s).card =
        2 ^ (n - 2) := by
    exact topLoss_completion_card_current
      R exponent hsLoss' hS
  rw [hsum,htopCard]
  calc
    S.card * 2 ^ (n - 3)
        ≤ 2 * 2 ^ (n - 3) :=
      Nat.mul_le_mul_right _ hScard
    _ = 2 ^ (n - 2) := by
      have hs : n - 3 + 1 = n - 2 := by omega
      rw [← hs, pow_succ]
      omega


theorem planar_top_secondLayerLoss_child_rank_lt
    {lam t delta : ℝ} {n : ℕ}
    (hcap : AngleCap p lam)
    (hn : 3 ≤ n)
    (hdelta0 : 0 ≤ delta)
    (hdeltaHalf : delta < (1 : ℝ) / 2)
    (ht : t = (n : ℝ) + delta)
    (hlam : lam = Real.pi / t)
    (C : ∀ i : ProjectionOrdered V,
      CentreProjectiveCycle
        (reindexedPoint_injective hp) i)
    {s w : ProjectionOrdered V}
    (hsLoss :
      let R :=
        planarStandardResidualColoring
          hp hcap (by omega : 1 ≤ n)
          hdelta0 (by linarith : delta < 1)
          ht hlam
      let exponent := planarCentreExponent hp C
      s ∈ projectedLossVertices R exponent)
    (hS : planarCentreExponent hp C s = n - 1)
    (hwLoss :
      let R :=
        planarStandardResidualColoring
          hp hcap (by omega : 1 ≤ n)
          hdelta0 (by linarith : delta < 1)
          ht hlam
      let exponent := planarCentreExponent hp C
      w ∈ projectedLossVertices R exponent)
    (hW : planarCentreExponent hp C w = n - 2) :
    let R :=
      planarStandardResidualColoring
        hp hcap (by omega : 1 ≤ n)
        hdelta0 (by linarith : delta < 1)
        ht hlam
    lossLayerHardStateRank n
        (retainedCompletionWords R w).card
        (planarCentreExponent hp C w)
      <
    lossLayerHardStateRank n
        (retainedCompletionWords R s).card
        (planarCentreExponent hp C s) := by
  let hn1 : 1 ≤ n := by omega
  let hdelta1 : delta < 1 := by linarith
  let R :=
    planarStandardResidualColoring
      hp hcap hn1 hdelta0 hdelta1 ht hlam
  let exponent := planarCentreExponent hp C
  have hsLoss' :
      s ∈ projectedLossVertices R exponent := by
    simpa [R,exponent,hn1,hdelta1] using hsLoss
  have hwLoss' :
      w ∈ projectedLossVertices R exponent := by
    simpa [R,exponent,hn1,hdelta1] using hwLoss
  have hsCard :
      (retainedCompletionWords R s).card =
        2 ^ (n - 2) :=
    topLoss_completion_card_current
      R exponent hsLoss' hS
  have hwCard :
      (retainedCompletionWords R w).card =
        2 ^ (n - 3) :=
    planar_secondLayerLoss_completion_card
      hp hcap hn hdelta0 hdeltaHalf
      ht hlam C hwLoss hW
  have hpayload :
      (retainedCompletionWords R w).card <
        (retainedCompletionWords R s).card := by
    rw [hwCard,hsCard]
    have hs : n - 3 + 1 = n - 2 := by omega
    rw [← hs, pow_succ]
    have hpos : 0 < 2 ^ (n - 3) := by positivity
    omega
  exact lossLayerHardStateRank_lt_of_payload_lt
    (n := n)
    (payload := (retainedCompletionWords R s).card)
    (payload' := (retainedCompletionWords R w).card)
    (exponent := planarCentreExponent hp C s)
    (exponent' := planarCentreExponent hp C w)
    (by rw [hS]; omega)
    (by rw [hW]; omega)
    hpayload

/-- Main genuine-planar hard remainder outlet. -/
theorem planar_centre_capacity_of_hard_words_fit_holes
    {lam t delta : ℝ} {n : ℕ}
    (hcap : AngleCap p lam)
    (hn : 1 ≤ n)
    (hdelta0 : 0 ≤ delta)
    (hdelta1 : delta < 1)
    (ht : t = (n : ℝ) + delta)
    (hlam : lam = Real.pi / t)
    (C : ∀ i : ProjectionOrdered V,
      CentreProjectiveCycle
        (reindexedPoint_injective hp) i)
    (hholes :
      let R :=
        planarStandardResidualColoring
          hp hcap hn hdelta0 hdelta1 ht hlam
      let exponent := planarCentreExponent hp C
      (saturatedOverlapWords R exponent).card +
          (lossCompletionWords R exponent).card
        ≤
      2 ^ n - (coveredCompletionWords R).card) :
    (∑ i : ProjectionOrdered V,
      2 ^ centreExponent (C i) t) ≤ 2 ^ n := by
  let R :=
    planarStandardResidualColoring
      hp hcap hn hdelta0 hdelta1 ht hlam
  let exponent := planarCentreExponent hp C
  have hexp :
      ∀ i, exponent i ≤ n :=
    planarCentreExponent_le_n
      hp hn hdelta0 hdelta1 ht C
  have hone :
      ∀ i, (active R i).card ≤
        n - exponent i + 1 := by
    exact planarStandardResidual_oneLayer_budget
      hp hcap hn hdelta0 hdelta1 ht hlam C
  have hcapCentre :
      (∑ i : ProjectionOrdered V, 2 ^ exponent i) ≤
        2 ^ n := by
    exact exponent_capacity_of_hard_words_fit_holes
      R exponent hexp hone hholes
  simpa [exponent, planarCentreExponent] using hcapCentre

#print axioms planarStandardResidualColoring
#print axioms planarCentreExponent_le_n
#print axioms planarCentreExponent_lt_n
#print axioms planarStandardResidual_oneLayer_budget
#print axioms planar_topLoss_word_four_exit_outlet
#print axioms planar_topLoss_word_layered_outlet
#print axioms planar_topLoss_secondLayer_companion_card_le_two
#print axioms planarTopSecondLayerLossVertices_card_le_two
#print axioms planar_top_secondLayerLoss_total_cube_le_top_cube
#print axioms planar_top_secondLayerLoss_child_rank_lt
#print axioms planar_centre_capacity_of_hard_words_fit_holes

end

end ProjectionOrdered
end JSP000404Research
