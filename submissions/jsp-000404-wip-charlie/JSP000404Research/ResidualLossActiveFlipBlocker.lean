import JSP000404Research.ResidualLossTrueHoleCoverPartition
import JSP000404Research.ResidualLossTranslatedBlock
import Mathlib.Tactic

/-!
# Canonical retained-active loss flips and genuine covered blockers

The exact loss ledger is valid for arbitrary flip-coordinate choices, but
non-active flips may leave the original owner cube fixed, leading to
avoidable artificial covered blockers.

We prove, from the ordinary one-layer exponent bound alone, that every
projected-loss vertex has a retained-active coordinate. For n >= 1 we
globally choose one such coordinate at each loss vertex.

If a word translated by this active choice is still globally covered,
its covering vertex MUST be different from its original loss owner.
The same retained coordinate must be active at both vertices.
This supplies a concrete, necessary two-owner structure for every
covered-blocker word, without claiming an injective payment.

No new geometric assumption and no admitted axiom are introduced.
-/

namespace JSP000404Research
namespace OrderedEdgeColoring

theorem projectedLoss_retainedActive_nonempty
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexp : ∀ v, exponent v ≤ n)
    {v : V}
    (hvLoss : v ∈ projectedLossVertices C exponent) :
    (retainedActive C v).Nonempty := by
  classical
  have hdata :=
    (mem_projectedLossVertices C exponent v).1 hvLoss
  have hcard :
      (retainedActive C v).card ≤ n := by
    exact Finset.card_le_univ (retainedActive C v)
  have hpos : 0 < (retainedActive C v).card := by
    dsimp [projectedFree] at hdata
    have hvexp := hexp v
    omega
  exact Finset.card_pos.mp hpos

/-- For n>=1, choose an actually active coordinate at every loss
owner, and any coordinate at every non-loss owner. -/
noncomputable def projectedLossActiveFlipChoice
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexp : ∀ v, exponent v ≤ n)
    (hn : 1 ≤ n) : V → Fin n :=
  fun v =>
    if h : v ∈ projectedLossVertices C exponent then
      Classical.choose
        (projectedLoss_retainedActive_nonempty C exponent hexp h)
    else ⟨0, by omega⟩

theorem projectedLossActiveFlipChoice_mem_retainedActive
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexp : ∀ v, exponent v ≤ n)
    (hn : 1 ≤ n)
    {v : V}
    (hvLoss : v ∈ projectedLossVertices C exponent) :
    projectedLossActiveFlipChoice C exponent hexp hn v ∈
      retainedActive C v := by
  classical
  simp only [projectedLossActiveFlipChoice, dif_pos hvLoss]
  exact Classical.choose_spec
    (projectedLoss_retainedActive_nonempty C exponent hexp hvLoss)

/-- A globally covered translated loss word, with active flips, is
necessarily blocked by a *different* vertex with the flip coordinate
active at both endpoints. It may still have several blockers, so this
does not imply an allocation or a charge to a true hole. -/
theorem translatedLossCoveredWord_has_distinct_shared_active_blocker
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexp : ∀ v, exponent v ≤ n)
    (honeLoss :
      ∀ v, (active C v).card ≤ n - exponent v + 1)
    (choice : V → Fin n)
    (hchoice : ∀ v ∈ projectedLossVertices C exponent,
      choice v ∈ retainedActive C v)
    {word : Fin n → Bool}
    (hcovered :
      word ∈ translatedLossCoveredWords C exponent choice) :
    ∃ v ∈ projectedLossVertices C exponent,
      ∃ w : V, v ≠ w ∧
        ∃ c : Fin n,
          c ∈ retainedActive C v ∧
          c ∈ retainedActive C w ∧
          word ∈ translatedCompletionWords C v c ∧
          word ∈ retainedCompletionWords C w := by
  classical
  have hpair := Finset.mem_inter.mp hcovered
  have hU := hpair.1
  have hK := hpair.2
  change word ∈ (Finset.univ : Finset (Fin n)).biUnion
    (fun c => translatedLossSliceWords C exponent choice c) at hU
  obtain ⟨c, _, hSlice⟩ := Finset.mem_biUnion.mp hU
  change word ∈ (lossCoordinateSlice C exponent choice c).biUnion
    (fun v => translatedCompletionWords C v c) at hSlice
  obtain ⟨v, hvSlice, hvWord⟩ := Finset.mem_biUnion.mp hSlice
  have hvData :=
    (mem_lossCoordinateSlice C exponent choice c v).1 hvSlice
  have hvLoss := hvData.1
  have hcActive : c ∈ retainedActive C v := by
    rw [← hvData.2]
    exact hchoice v hvLoss
  obtain ⟨w, hwFibre⟩ :=
    (mem_coveredCompletionWords C word).1 hK
  have hwBlock : word ∈ retainedCompletionWords C w :=
    (mem_completionFibre C word w).1 hwFibre
  have hvneq : v ≠ w := by
    intro heq
    subst w
    have hdisj :=
      translatedCompletionWords_disjoint_original_of_active
        C hcActive
    exact Finset.disjoint_left.mp hdisj hvWord hwBlock
  have hsource :
      flipBoolWordAt word c ∈ retainedCompletionWords C v :=
    (mem_translatedCompletionWords C v c word).1 hvWord
  have hdest :
      flipBoolWordAt (flipBoolWordAt word c) c ∈
        retainedCompletionWords C w := by
    simpa only [flipBoolWordAt_involutive] using hwBlock
  have hcBlocked :=
    loss_translated_blocker_active
      C exponent hexp honeLoss
      hvLoss hcActive hvneq hsource hdest
  exact ⟨v, hvLoss, w, hvneq,
    c, hcActive, hcBlocked, hvWord, hwBlock⟩

/-- The preceding blocker theorem holds for a globally defined,
actually retained-active choice without any independent choice axiom. -/
theorem activeChoice_translatedLossCoveredWord_has_shared_blocker
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexp : ∀ v, exponent v ≤ n)
    (honeLoss :
      ∀ v, (active C v).card ≤ n - exponent v + 1)
    (hn : 1 ≤ n)
    {word : Fin n → Bool}
    (hcovered :
      word ∈ translatedLossCoveredWords C exponent
        (projectedLossActiveFlipChoice C exponent hexp hn)) :
    ∃ v ∈ projectedLossVertices C exponent,
      ∃ w : V, v ≠ w ∧
        ∃ c : Fin n,
          c ∈ retainedActive C v ∧
          c ∈ retainedActive C w ∧
          word ∈ translatedCompletionWords C v c ∧
          word ∈ retainedCompletionWords C w :=
  translatedLossCoveredWord_has_distinct_shared_active_blocker
    C exponent hexp honeLoss
    (projectedLossActiveFlipChoice C exponent hexp hn)
    (fun v hv =>
      projectedLossActiveFlipChoice_mem_retainedActive
        C exponent hexp hn hv)
    hcovered

#print axioms projectedLoss_retainedActive_nonempty
#print axioms projectedLossActiveFlipChoice_mem_retainedActive
#print axioms translatedLossCoveredWord_has_distinct_shared_active_blocker
#print axioms activeChoice_translatedLossCoveredWord_has_shared_blocker

end OrderedEdgeColoring
end JSP000404Research
