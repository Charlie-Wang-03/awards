import JSP000404Research.PlanarLowerBranchHardWordInjection
import Mathlib.Combinatorics.Hall.Basic
import Mathlib.Tactic

/-!
# Hall outlet for the all-cardinality hard-word injection

The final lower-branch payment need not be constructed by one explicit
augmenting algorithm.  Mathlib already provides Hall's marriage theorem for
an indexed family of finite candidate sets.

For every hard projection word x, choose a finite set candidates(x) of Boolean
holes.  If

* every candidate really is a projection hole, and
* every finite set S of hard words satisfies Hall expansion

    card S <= card (union_{x in S} candidates(x)),

then Hall gives distinct representatives.  These representatives define the
hard-word injection required by PlanarLowerBranchHardWordInjection, and hence
the sharp dyadic capacity.

This is the correct global interface for combining the local branching and
blocker-expansion lemmas.
-/

namespace JSP000404Research
namespace OrderedEdgeColoring

theorem hardProjectionWords_injection_of_hall
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (candidates :
      {word : Fin n → Bool //
        word ∈ hardProjectionWords C exponent} →
      Finset (Fin n → Bool))
    (hholes :
      ∀ x,
        candidates x ⊆ projectionHoleWords C)
    (hHall :
      ∀ s : Finset
        {word : Fin n → Bool //
          word ∈ hardProjectionWords C exponent},
        s.card ≤ (s.biUnion candidates).card) :
    ∃ f :
      {word : Fin n → Bool //
        word ∈ hardProjectionWords C exponent} →
      {word : Fin n → Bool //
        word ∈ projectionHoleWords C},
      Function.Injective f := by
  classical
  obtain ⟨g,hgInj,hgMem⟩ :=
    (Finset.all_card_le_biUnion_card_iff_exists_injective
      candidates).1 hHall
  let f :
      {word : Fin n → Bool //
        word ∈ hardProjectionWords C exponent} →
      {word : Fin n → Bool //
        word ∈ projectionHoleWords C} :=
    fun x => ⟨g x, hholes x (hgMem x)⟩
  refine ⟨f, ?_⟩
  intro x y hxy
  apply Subtype.ext
  apply hgInj
  exact congrArg Subtype.val hxy

theorem exponent_capacity_of_hall_hard_word_candidates
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexp : ∀ v, exponent v ≤ n)
    (honeLoss :
      ∀ v, (active C v).card ≤ n - exponent v + 1)
    (candidates :
      {word : Fin n → Bool //
        word ∈ hardProjectionWords C exponent} →
      Finset (Fin n → Bool))
    (hholes :
      ∀ x,
        candidates x ⊆ projectionHoleWords C)
    (hHall :
      ∀ s : Finset
        {word : Fin n → Bool //
          word ∈ hardProjectionWords C exponent},
        s.card ≤ (s.biUnion candidates).card) :
    (∑ v, 2 ^ exponent v) ≤ 2 ^ n := by
  obtain ⟨f,hf⟩ :=
    hardProjectionWords_injection_of_hall
      C exponent candidates hholes hHall
  exact exponent_capacity_of_hardProjectionWords_injection
    C exponent hexp honeLoss f hf

#print axioms hardProjectionWords_injection_of_hall
#print axioms exponent_capacity_of_hall_hard_word_candidates

end OrderedEdgeColoring

namespace ProjectionOrdered

open OrderedEdgeColoring
open DirectionData
open scoped BigOperators

theorem planar_lowerBranch_capacity_of_hall_candidates
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
      ∀ i : ProjectionOrdered V,
        CentreProjectiveCycle (reindexedPoint_injective hp) i)
    (candidates :
      letI : LinearOrder (ProjectionOrdered V) :=
        projectionLinearOrder hp
      let htpos : 0 < t :=
        sendov_scale_pos hn hdelta0 ht
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
      {word : Fin n → Bool //
        word ∈ hardProjectionWords B exponent} →
      Finset (Fin n → Bool))
    (hholes :
      letI : LinearOrder (ProjectionOrdered V) :=
        projectionLinearOrder hp
      let htpos : 0 < t :=
        sendov_scale_pos hn hdelta0 ht
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
      ∀ x, candidates x ⊆ projectionHoleWords B)
    (hHall :
      letI : LinearOrder (ProjectionOrdered V) :=
        projectionLinearOrder hp
      let htpos : 0 < t :=
        sendov_scale_pos hn hdelta0 ht
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
      ∀ s : Finset
        {word : Fin n → Bool //
          word ∈ hardProjectionWords B exponent},
        s.card ≤ (s.biUnion candidates).card) :
    ∑ i : ProjectionOrdered V, 2 ^ centreExponent (C i) t
      ≤ 2 ^ n := by
  letI : LinearOrder (ProjectionOrdered V) :=
    projectionLinearOrder hp
  have htpos : 0 < t :=
    sendov_scale_pos hn hdelta0 ht
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
    simpa [B,D,exponent] using
      planarStandardResidual_active_card_le_oneLayer
        hp hcap hn hdelta0 hdelta1 ht hlam i (C i)

  have hholes' :
      ∀ x, candidates x ⊆ projectionHoleWords B := by
    simpa [B,D,exponent] using hholes

  have hHall' :
      ∀ s : Finset
        {word : Fin n → Bool //
          word ∈ hardProjectionWords B exponent},
        s.card ≤ (s.biUnion candidates).card := by
    simpa [B,D,exponent] using hHall

  have hcap' :=
    exponent_capacity_of_hall_hard_word_candidates
      B exponent hexp honeLoss candidates hholes' hHall'
  simpa [exponent] using hcap'

#print axioms planar_lowerBranch_capacity_of_hall_candidates

end ProjectionOrdered
end JSP000404Research
