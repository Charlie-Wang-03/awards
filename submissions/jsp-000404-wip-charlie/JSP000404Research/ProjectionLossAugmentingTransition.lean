import JSP000404Research.ResidualSingleFibreTransition
import JSP000404Research.ResidualLossTranslatedBlock
import JSP000404Research.ProjectionLossFlipCoordinate
import JSP000404Research.ResidualSingleFibreBranching
import Mathlib.Tactic

/-!
# Projected-loss words enter the unified single-fibre augmenting machine

A projected-loss completion cube is disjoint from every other completion cube.
Therefore every word of that cube has completion-fibre cardinality exactly one.

In the planar lower branch, ProjectionLossFlipCoordinate supplies one retained
active coordinate c for the whole loss cube. Flipping c takes each loss word
out of its owner cube. The generic single-fibre transition then says that the
flipped word either

* is a genuine Boolean hole,
* is singly covered by a new blocker, or
* is doubly covered by a residual-overlap pair,

and every blocker activates c with the opposite canonical bit.

Thus lossCompletionWords and saturated-overlap words can now be treated inside
one multiplicity-0/1/2 augmenting state machine.
-/

namespace JSP000404Research
namespace OrderedEdgeColoring

theorem projectedLoss_word_is_singleCompletionWord
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexp : ∀ v, exponent v ≤ n)
    (honeLoss :
      ∀ v, (active C v).card ≤ n - exponent v + 1)
    {v : V}
    (hvLoss : v ∈ projectedLossVertices C exponent)
    {word : Fin n → Bool}
    (hword : word ∈ retainedCompletionWords C v) :
    IsSingleCompletionWord C v word := by
  refine ⟨hword, ?_⟩
  intro w hw
  by_contra hvw
  have hdisj :=
    projectedLoss_completion_disjoint
      C exponent hexp honeLoss hvLoss hvw
  exact Finset.disjoint_left.mp hdisj hword hw

theorem projectedLoss_flip_hole_or_controlled_blocker
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexp : ∀ v, exponent v ≤ n)
    (honeLoss :
      ∀ v, (active C v).card ≤ n - exponent v + 1)
    {v : V}
    (hvLoss : v ∈ projectedLossVertices C exponent)
    {c : Fin n}
    (hc : c ∈ retainedActive C v)
    {word : Fin n → Bool}
    (hword : word ∈ retainedCompletionWords C v) :
    let y := flipBoolWordAt word c
    ((completionFibre C y).card = 0)
    ∨
    ((completionFibre C y).card = 1 ∨
      (completionFibre C y).card = 2) ∧
      ∀ w : V,
        y ∈ retainedCompletionWords C w →
        w ≠ v ∧
        c ∈ retainedActive C w ∧
        retainedBit C w c = !(retainedBit C v c) := by
  have hsingle :=
    projectedLoss_word_is_singleCompletionWord
      C exponent hexp honeLoss hvLoss hword
  exact single_flip_hole_or_controlled_blocker
    C hsingle hc

#print axioms projectedLoss_word_is_singleCompletionWord
#print axioms projectedLoss_flip_hole_or_controlled_blocker

end OrderedEdgeColoring

namespace ProjectionOrdered

open OrderedEdgeColoring
open DirectionData

theorem planar_projectedLoss_uniform_augmenting_coordinate
    {V : Type*} [Fintype V]
    {p : V → Plane}
    (hp : Function.Injective p)
    {lam t delta : ℝ} {n : ℕ}
    (hcap : AngleCap p lam)
    (hn : 1 ≤ n)
    (hdelta0 : 0 ≤ delta)
    (hdeltaHalf : delta < (1 : ℝ) / 2)
    (ht : t = (n : ℝ) + delta)
    (hlam : lam = Real.pi / t)
    (C :
      ∀ i : ProjectionOrdered V,
        CentreProjectiveCycle (reindexedPoint_injective hp) i)
    (i : ProjectionOrdered V)
    (hloss :
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
        fun j => centreExponent (C j) t
      i ∈ projectedLossVertices B exponent) :
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
      fun j => centreExponent (C j) t
    ∃ c : Fin n,
      c ∈ retainedActive B i ∧
      ∀ word : Fin n → Bool,
        word ∈ retainedCompletionWords B i →
        let y := flipBoolWordAt word c
        ((completionFibre B y).card = 0)
        ∨
        ((completionFibre B y).card = 1 ∨
          (completionFibre B y).card = 2) ∧
          ∀ w : ProjectionOrdered V,
            y ∈ retainedCompletionWords B w →
            w ≠ i ∧
            c ∈ retainedActive B w ∧
            retainedBit B w c = !(retainedBit B i c) := by
  letI : LinearOrder (ProjectionOrdered V) :=
    projectionLinearOrder hp
  have hdelta1 : delta < 1 := by linarith
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
    fun j => centreExponent (C j) t

  have hloss' : i ∈ projectedLossVertices B exponent := by
    simpa [B,D,exponent] using hloss

  have hprofile :=
    genericProjection_lowerBranch_profile_hypotheses
      hp hcap hn hdelta0 hdelta1 ht hlam C
  have hexp : ∀ j, exponent j ≤ n := by
    intro j
    exact Nat.le_of_lt (by simpa [exponent] using hprofile.1 j)
  have hone :
      ∀ j, (active B j).card ≤ n - exponent j + 1 := by
    intro j
    simpa [B,D,exponent] using hprofile.2 j

  obtain ⟨c,hc,hflipExit⟩ :=
    planar_projectedLoss_has_retained_active_flip_coordinate
      hp hcap hn hdelta0 hdeltaHalf ht hlam C i
      (by simpa [B,D,exponent] using hloss')

  refine ⟨c,hc,?_⟩
  intro word hword
  exact projectedLoss_flip_hole_or_controlled_blocker
    B exponent hexp hone hloss' hc hword


theorem planar_projectedLoss_two_exit_expansion
    {V : Type*} [Fintype V]
    {p : V → Plane}
    (hp : Function.Injective p)
    {lam t delta : ℝ} {n : ℕ}
    (hcap : AngleCap p lam)
    (hn : 1 ≤ n)
    (hdelta0 : 0 ≤ delta)
    (hdeltaHalf : delta < (1 : ℝ) / 2)
    (ht : t = (n : ℝ) + delta)
    (hlam : lam = Real.pi / t)
    (C :
      ∀ i : ProjectionOrdered V,
        CentreProjectiveCycle (reindexedPoint_injective hp) i)
    (i : ProjectionOrdered V)
    (hloss :
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
        fun j => centreExponent (C j) t
      i ∈ projectedLossVertices B exponent) :
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
      fun j => centreExponent (C j) t
    ∃ c d : Fin n,
      c ≠ d ∧
      c ∈ retainedActive B i ∧
      d ∈ retainedActive B i ∧
      ∀ word : Fin n → Bool,
        word ∈ retainedCompletionWords B i →
        (
          (completionFibre B (flipBoolWordAt word c)).card = 0
          ∨
          (completionFibre B (flipBoolWordAt word d)).card = 0
          ∨
          ∃ w z : ProjectionOrdered V,
            w ≠ z ∧
            flipBoolWordAt word c ∈ retainedCompletionWords B w ∧
            flipBoolWordAt word d ∈ retainedCompletionWords B z
        ) := by
  letI : LinearOrder (ProjectionOrdered V) :=
    projectionLinearOrder hp
  have hdelta1 : delta < 1 := by linarith
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
    fun j => centreExponent (C j) t

  have hloss' : i ∈ projectedLossVertices B exponent := by
    simpa [B,D,exponent] using hloss

  have hprofile :=
    genericProjection_lowerBranch_profile_hypotheses
      hp hcap hn hdelta0 hdelta1 ht hlam C
  have hexp : ∀ j, exponent j ≤ n := by
    intro j
    exact Nat.le_of_lt (by simpa [exponent] using hprofile.1 j)
  have hone :
      ∀ j, (active B j).card ≤ n - exponent j + 1 := by
    intro j
    simpa [B,D,exponent] using hprofile.2 j

  obtain ⟨c,d,hadj,hc,hd⟩ :=
    planar_projectedLoss_has_adjacent_retained_active_pair
      hp hcap hn hdelta0 hdeltaHalf ht hlam C i
      (by simpa [B,D,exponent] using hloss')

  have hcd : c ≠ d := by
    intro h
    have hv := congrArg Fin.val h
    rw [hadj] at hv
    omega

  refine ⟨c,d,hcd,hc,hd,?_⟩
  intro word hword

  have hsingle :=
    projectedLoss_word_is_singleCompletionWord
      B exponent hexp hone hloss' hword

  by_cases hcHole :
      (completionFibre B (flipBoolWordAt word c)).card = 0
  · exact Or.inl hcHole
  · by_cases hdHole :
        (completionFibre B (flipBoolWordAt word d)).card = 0
    · exact Or.inr (Or.inl hdHole)
    · right
      right
      have hcNonempty :
          (completionFibre B (flipBoolWordAt word c)).Nonempty := by
        apply Finset.card_pos.mp
        have hle :=
          completionFibre_card_le_two B
            (flipBoolWordAt word c)
        omega
      have hdNonempty :
          (completionFibre B (flipBoolWordAt word d)).Nonempty := by
        apply Finset.card_pos.mp
        have hle :=
          completionFibre_card_le_two B
            (flipBoolWordAt word d)
        omega
      exact two_single_flips_nonempty_fibres_give_two_blockers
        B hsingle hc hd hcd hcNonempty hdNonempty

#print axioms planar_projectedLoss_uniform_augmenting_coordinate
#print axioms planar_projectedLoss_two_exit_expansion

end ProjectionOrdered
end JSP000404Research
