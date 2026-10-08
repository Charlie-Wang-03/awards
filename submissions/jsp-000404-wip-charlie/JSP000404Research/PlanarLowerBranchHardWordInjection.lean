import JSP000404Research.ProjectionResidualHardRemainder
import JSP000404Research.PlanarStandardResidualBudget
import Mathlib.Tactic

/-!
# All-cardinality lower branch from one explicit hard-word injection

The residual accounting has reduced the planar lower branch to two concrete
finite sets of n-bit Boolean words:

* hard demand:
    saturatedOverlapWords ∪ lossCompletionWords;
* holes:
    the complement of coveredCompletionWords in the ambient Boolean cube.

Loss words are disjoint from every overlap word, so the cardinality of the
hard demand is exactly the sum appearing in the hard-remainder theorem.

Consequently an explicit injection from hard demand words to Boolean holes is
a complete certificate for the lower-branch all-cardinality dyadic capacity.
This file packages that final interface.
-/

namespace JSP000404Research
namespace OrderedEdgeColoring

noncomputable def hardProjectionWords
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ) :
    Finset (Fin n → Bool) :=
  saturatedOverlapWords C exponent ∪
    lossCompletionWords C exponent

noncomputable def projectionHoleWords
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1)) :
    Finset (Fin n → Bool) :=
  (Finset.univ : Finset (Fin n → Bool)) \
    coveredCompletionWords C

theorem hardProjectionWords_card_eq
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexp : ∀ v, exponent v ≤ n)
    (honeLoss :
      ∀ v, (active C v).card ≤ n - exponent v + 1) :
    (hardProjectionWords C exponent).card =
      (saturatedOverlapWords C exponent).card +
        (lossCompletionWords C exponent).card := by
  classical
  unfold hardProjectionWords
  apply Finset.card_union_of_disjoint
  have hdisj :
      Disjoint
        (lossCompletionWords C exponent)
        (saturatedOverlapWords C exponent) := by
    apply Finset.disjoint_of_subset_right Finset.sdiff_subset
    exact lossCompletionWords_disjoint_overlapCompletionWords
      C exponent hexp honeLoss
  exact hdisj.symm

theorem projectionHoleWords_card
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1)) :
    (projectionHoleWords C).card =
      2 ^ n - (coveredCompletionWords C).card := by
  classical
  unfold projectionHoleWords
  rw [Finset.card_sdiff_of_subset (Finset.subset_univ _)]
  simp [Fintype.card_fun]

theorem exponent_capacity_of_hardProjectionWords_injection
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexp : ∀ v, exponent v ≤ n)
    (honeLoss :
      ∀ v, (active C v).card ≤ n - exponent v + 1)
    (f :
      {word // word ∈ hardProjectionWords C exponent} →
      {word // word ∈ projectionHoleWords C})
    (hf : Function.Injective f) :
    (∑ v, 2 ^ exponent v) ≤ 2 ^ n := by
  have hcard :
      (hardProjectionWords C exponent).card ≤
        (projectionHoleWords C).card := by
    simpa only [Fintype.card_coe] using
      Fintype.card_le_of_injective f hf
  rw [hardProjectionWords_card_eq C exponent hexp honeLoss,
      projectionHoleWords_card C] at hcard
  exact exponent_capacity_of_hard_words_fit_holes
    C exponent hexp honeLoss hcard

#print axioms hardProjectionWords_card_eq
#print axioms projectionHoleWords_card
#print axioms exponent_capacity_of_hardProjectionWords_injection

end OrderedEdgeColoring

namespace ProjectionOrdered

open OrderedEdgeColoring
open DirectionData
open scoped BigOperators

private theorem planarHard_scale_pos
    {n : ℕ} {delta t : ℝ}
    (hn : 1 ≤ n) (hdelta0 : 0 ≤ delta)
    (ht : t = (n : ℝ) + delta) : 0 < t := by
  rw [ht]
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  linarith

theorem planar_lowerBranch_capacity_of_hardWordInjection
    {V : Type*} [Fintype V]
    {p : V → Plane}
    (hp : Function.Injective p)
    {lam t delta : ℝ} {n : ℕ}
    (hcap : AngleCap p lam)
    (hn : 1 ≤ n)
    (hdelta0 : 0 ≤ delta)
    (hdelta1 : delta < 1)
    (ht : t = (n : ℝ) + delta)
    (hlam : lam = Real.pi / t)
    (C :
      letI : LinearOrder (ProjectionOrdered V) :=
        projectionLinearOrder hp
      ∀ i : ProjectionOrdered V,
        CentreProjectiveCycle (reindexedPoint_injective hp) i)
    (f :
      letI : LinearOrder (ProjectionOrdered V) :=
        projectionLinearOrder hp
      let htpos : 0 < t :=
        planarHard_scale_pos hn hdelta0 ht
      let D :=
        genericDirectionData_sendov hp hcap htpos hlam
      let hwidth : t < (n + 1 : ℕ) := by
        rw [ht]
        exact_mod_cast
          (show (n : ℝ) + delta < (n : ℝ) + 1 by linarith)
      let B :=
        standardResidualColoring D n hwidth
      let exponent : ProjectionOrdered V → ℕ :=
        fun i => centreExponent (C i) t
      {word // word ∈ hardProjectionWords B exponent} →
        {word // word ∈ projectionHoleWords B})
    (hf :
      letI : LinearOrder (ProjectionOrdered V) :=
        projectionLinearOrder hp
      Function.Injective f) :
    letI : LinearOrder (ProjectionOrdered V) :=
      projectionLinearOrder hp
    ∑ i : ProjectionOrdered V, 2 ^ centreExponent (C i) t
      ≤ 2 ^ n := by
  letI : LinearOrder (ProjectionOrdered V) :=
    projectionLinearOrder hp
  have htpos : 0 < t :=
    planarHard_scale_pos hn hdelta0 ht
  have hwidthR : t < (n : ℝ) + 1 := by
    rw [ht]
    linarith
  have hwidth : t < (n + 1 : ℕ) := by
    exact_mod_cast hwidthR

  let D :=
    genericDirectionData_sendov hp hcap htpos hlam
  let B : OrderedEdgeColoring (ProjectionOrdered V) (n + 1) :=
    standardResidualColoring D n hwidth
  let exponent : ProjectionOrdered V → ℕ :=
    fun i => centreExponent (C i) t

  have hexp : ∀ i, exponent i ≤ n := by
    intro i
    exact Nat.le_of_lt
      (centreExponent_lt_n
        (C i) n delta t hn hdelta0 hdelta1 ht)

  have honeLoss :
      ∀ i, (active B i).card ≤ n - exponent i + 1 := by
    intro i
    simpa [B, D, exponent] using
      planarStandardResidual_active_card_le_oneLayer
        hp hcap hn hdelta0 hdelta1 ht hlam i (C i)

  have hcap' :=
    exponent_capacity_of_hardProjectionWords_injection
      B exponent hexp honeLoss f hf
  simpa [exponent] using hcap'

#print axioms planar_lowerBranch_capacity_of_hardWordInjection

end ProjectionOrdered
end JSP000404Research
