import JSP000404Research.ResidualEnlargedCollisionSimpleGraph
import Mathlib.Tactic

/-!
# Bounded-multiplicity accounting for enlarged candidate blocks

The long-cycle counting argument does not intrinsically require girth > 3.
Its real combinatorial hypothesis is only that every Boolean word belongs to
at most two core candidate blocks.

Under this fibre-multiplicity bound:

* total block mass = union mass + double-covered mass;
* total shared mass = twice the double-covered mass;
* in a deficient core, double-covered mass equals total local slack plus the
  positive deficiency;
* hence some vertex is shared-mass overloaded;
* the existing profile argument then forces that overloaded vertex to be exact
  or a top projected-loss vertex.

Consequently every deficient core admits a sharper global dichotomy:
either some Boolean word has multiplicity at least three, or there is an
exact/top-loss overload.  This replaces the graph-theoretic
"triangle versus long cycle" split by the actual multiplicity obstruction.
-/

namespace JSP000404Research
namespace OrderedEdgeColoring

theorem coreEnlargedCandidateFibre_card_eq_two_of_shared_of_card_le_two
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    {T : Finset V}
    (hle :
      ∀ word : Fin n → Bool,
        (coreEnlargedCandidateFibre C exponent T word).card ≤ 2)
    {v : V}
    (hvT : v ∈ T)
    {word : Fin n → Bool}
    (hshared :
      word ∈ sharedBlockWords
        (enlargedProjectedCandidateBlock C exponent)
        T v) :
    (coreEnlargedCandidateFibre C exponent T word).card = 2 := by
  have hvF :=
    mem_coreEnlargedCandidateFibre_of_shared
      C exponent hvT hshared
  have hdata :=
    sharedBlockWords_has_other_block
      (enlargedProjectedCandidateBlock C exponent)
      hshared
  obtain ⟨_hvWord,w,hwT,hwv,hwWord⟩ := hdata
  have hwF :
      w ∈ coreEnlargedCandidateFibre C exponent T word :=
    (mem_coreEnlargedCandidateFibre
      C exponent T word w).2 ⟨hwT,hwWord⟩
  have htwo :
      2 ≤ (coreEnlargedCandidateFibre C exponent T word).card :=
    Finset.two_le_card.mpr ⟨v,hvF,w,hwF,hwv.symm⟩
  have hup := hle word
  omega

theorem shared_iff_mem_fibre_and_card_eq_two_of_card_le_two
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    {T : Finset V}
    (hle :
      ∀ word : Fin n → Bool,
        (coreEnlargedCandidateFibre C exponent T word).card ≤ 2)
    {v : V}
    (hvT : v ∈ T)
    {word : Fin n → Bool} :
    word ∈ sharedBlockWords
        (enlargedProjectedCandidateBlock C exponent)
        T v
      ↔
    v ∈ coreEnlargedCandidateFibre C exponent T word ∧
      (coreEnlargedCandidateFibre C exponent T word).card = 2 := by
  constructor
  · intro hshared
    exact ⟨
      mem_coreEnlargedCandidateFibre_of_shared
        C exponent hvT hshared,
      coreEnlargedCandidateFibre_card_eq_two_of_shared_of_card_le_two
        C exponent hle hvT hshared
    ⟩
  · rintro ⟨hvF,hcard⟩
    have hvData :=
      (mem_coreEnlargedCandidateFibre
        C exponent T word v).1 hvF
    have hexists :
        ∃ w ∈ coreEnlargedCandidateFibre C exponent T word,
          w ≠ v := by
      by_contra hnot
      push_neg at hnot
      have hsub :
          coreEnlargedCandidateFibre C exponent T word ⊆ {v} := by
        intro w hw
        simpa [hnot w hw]
      have hc := Finset.card_le_card hsub
      simp [hcard] at hc
    obtain ⟨w,hwF,hwv⟩ := hexists
    have hwData :=
      (mem_coreEnlargedCandidateFibre
        C exponent T word w).1 hwF
    apply Finset.mem_inter.mpr
    constructor
    · exact hvData.2
    · apply Finset.mem_biUnion.mpr
      exact ⟨w,
        Finset.mem_erase.mpr ⟨hwv,hwData.1⟩,
        hwData.2⟩

theorem boundedMultiplicity_sum_shared_cards_eq_two_mul_doubleCovered
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    {T : Finset V}
    (hle :
      ∀ word : Fin n → Bool,
        (coreEnlargedCandidateFibre C exponent T word).card ≤ 2) :
    (∑ v ∈ T,
      (sharedBlockWords
        (enlargedProjectedCandidateBlock C exponent)
        T v).card)
      =
    2 * (coreDoubleCoveredWords C exponent T).card := by
  classical
  have hpoint :
      ∀ word : Fin n → Bool,
        (∑ v ∈ T,
          if word ∈ sharedBlockWords
              (enlargedProjectedCandidateBlock C exponent)
              T v
          then 1 else 0)
        =
        if word ∈ coreDoubleCoveredWords C exponent T
        then 2 else 0 := by
    intro word
    by_cases hdouble :
        word ∈ coreDoubleCoveredWords C exponent T
    · have hcard :=
        (mem_coreDoubleCoveredWords C exponent T word).1 hdouble
      have hfilterEq :
          T.filter
              (fun v =>
                word ∈ sharedBlockWords
                  (enlargedProjectedCandidateBlock C exponent)
                  T v)
            =
          coreEnlargedCandidateFibre C exponent T word := by
        ext v
        simp only [Finset.mem_filter]
        constructor
        · rintro ⟨hvT,hshared⟩
          exact mem_coreEnlargedCandidateFibre_of_shared
            C exponent hvT hshared
        · intro hvF
          have hvData :=
            (mem_coreEnlargedCandidateFibre
              C exponent T word v).1 hvF
          refine ⟨hvData.1,?_⟩
          exact
            (shared_iff_mem_fibre_and_card_eq_two_of_card_le_two
              C exponent hle hvData.1).2
              ⟨hvF,hcard⟩
      calc
        (∑ v ∈ T,
          if word ∈ sharedBlockWords
              (enlargedProjectedCandidateBlock C exponent)
              T v
          then 1 else 0)
          =
        (T.filter
          (fun v =>
            word ∈ sharedBlockWords
              (enlargedProjectedCandidateBlock C exponent)
              T v)).card := by
            symm
            exact Finset.card_filter _ _
        _ =
        (coreEnlargedCandidateFibre C exponent T word).card := by
          rw [hfilterEq]
        _ = 2 := hcard
        _ =
        if word ∈ coreDoubleCoveredWords C exponent T
        then 2 else 0 := by simp [hdouble]
    · have hnone :
          ∀ v ∈ T,
            word ∉ sharedBlockWords
              (enlargedProjectedCandidateBlock C exponent)
              T v := by
        intro v hvT hshared
        have hcard :=
          coreEnlargedCandidateFibre_card_eq_two_of_shared_of_card_le_two
            C exponent hle hvT hshared
        exact hdouble
          ((mem_coreDoubleCoveredWords
            C exponent T word).2 hcard)
      simp [hdouble,hnone]

  calc
    (∑ v ∈ T,
      (sharedBlockWords
        (enlargedProjectedCandidateBlock C exponent)
        T v).card)
      =
    ∑ v ∈ T,
      ∑ word : Fin n → Bool,
        if word ∈ sharedBlockWords
            (enlargedProjectedCandidateBlock C exponent)
            T v
        then 1 else 0 := by
          apply Finset.sum_congr rfl
          intro v hvT
          symm
          exact Finset.card_eq_sum_ite
            (Finset.subset_univ
              (sharedBlockWords
                (enlargedProjectedCandidateBlock C exponent)
                T v))
    _ =
    ∑ word : Fin n → Bool,
      ∑ v ∈ T,
        if word ∈ sharedBlockWords
            (enlargedProjectedCandidateBlock C exponent)
            T v
        then 1 else 0 := by
          rw [Finset.sum_comm]
    _ =
    ∑ word : Fin n → Bool,
      if word ∈ coreDoubleCoveredWords C exponent T
      then 2 else 0 := by
          apply Finset.sum_congr rfl
          intro word hword
          exact hpoint word
    _ =
    2 * (coreDoubleCoveredWords C exponent T).card := by
      have hcard :
          (coreDoubleCoveredWords C exponent T).card
            =
          ∑ word : Fin n → Bool,
            if word ∈ coreDoubleCoveredWords C exponent T
            then 1 else 0 :=
        Finset.card_eq_sum_ite
          (Finset.subset_univ
            (coreDoubleCoveredWords C exponent T))
      rw [hcard, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro word hword
      by_cases hmem :
          word ∈ coreDoubleCoveredWords C exponent T
      · simp [hmem]
      · simp [hmem]

theorem boundedMultiplicity_sum_block_cards_eq_union_add_double
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (T : Finset V)
    (hle :
      ∀ word : Fin n → Bool,
        (coreEnlargedCandidateFibre C exponent T word).card ≤ 2) :
    (∑ v ∈ T,
      (enlargedProjectedCandidateBlock C exponent v).card)
      =
    (T.biUnion
      (enlargedProjectedCandidateBlock C exponent)).card
      +
    (coreDoubleCoveredWords C exponent T).card := by
  rw [← sum_coreEnlargedCandidateFibre_cards_eq_sum_block_cards
    C exponent T]
  exact sum_fibre_cards_eq_union_add_double_of_card_le_two
    C exponent T hle

theorem boundedMultiplicity_doubleCovered_eq_totalSlack_add_deficiency
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexpLt : ∀ x, exponent x < n)
    (hexp : ∀ x, exponent x ≤ n)
    (honeLoss :
      ∀ x, (active C x).card ≤ n - exponent x + 1)
    {T : Finset V}
    (hdef :
      BlockDeficient
        (fun x => 2 ^ exponent x)
        (enlargedProjectedCandidateBlock C exponent)
        T)
    (hle :
      ∀ word : Fin n → Bool,
        (coreEnlargedCandidateFibre C exponent T word).card ≤ 2) :
    (coreDoubleCoveredWords C exponent T).card
      =
    (∑ v ∈ T,
      ((enlargedProjectedCandidateBlock C exponent v).card -
        2 ^ exponent v))
      +
    blockDeficiencyAmount
      (fun x => 2 ^ exponent x)
      (enlargedProjectedCandidateBlock C exponent)
      T := by
  classical
  have hcount :=
    boundedMultiplicity_sum_block_cards_eq_union_add_double
      C exponent T hle
  have hlocal :
      ∀ v : V,
        2 ^ exponent v ≤
          (enlargedProjectedCandidateBlock C exponent v).card :=
    enlargedProjectedCandidateBlock_local_capacity
      C exponent hexpLt hexp honeLoss
  have hslackAdd :
      (∑ v ∈ T,
        ((enlargedProjectedCandidateBlock C exponent v).card -
          2 ^ exponent v))
        +
      (∑ v ∈ T, 2 ^ exponent v)
      =
      ∑ v ∈ T,
        (enlargedProjectedCandidateBlock C exponent v).card := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro v hvT
    exact Nat.sub_add_cancel (hlocal v)
  have hdef' :
      (T.biUnion
        (enlargedProjectedCandidateBlock C exponent)).card
        <
      ∑ v ∈ T, 2 ^ exponent v := hdef
  unfold blockDeficiencyAmount
  omega

theorem boundedMultiplicity_sum_shared_eq_two_slack_add_two_deficiency
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexpLt : ∀ x, exponent x < n)
    (hexp : ∀ x, exponent x ≤ n)
    (honeLoss :
      ∀ x, (active C x).card ≤ n - exponent x + 1)
    {T : Finset V}
    (hdef :
      BlockDeficient
        (fun x => 2 ^ exponent x)
        (enlargedProjectedCandidateBlock C exponent)
        T)
    (hle :
      ∀ word : Fin n → Bool,
        (coreEnlargedCandidateFibre C exponent T word).card ≤ 2) :
    (∑ v ∈ T,
      (sharedBlockWords
        (enlargedProjectedCandidateBlock C exponent)
        T v).card)
      =
    2 *
      (∑ v ∈ T,
        ((enlargedProjectedCandidateBlock C exponent v).card -
          2 ^ exponent v))
      +
    2 *
      blockDeficiencyAmount
        (fun x => 2 ^ exponent x)
        (enlargedProjectedCandidateBlock C exponent)
        T := by
  have hshared :=
    boundedMultiplicity_sum_shared_cards_eq_two_mul_doubleCovered
      C exponent hle
  have hdouble :=
    boundedMultiplicity_doubleCovered_eq_totalSlack_add_deficiency
      C exponent hexpLt hexp honeLoss hdef hle
  rw [hdouble] at hshared
  omega

theorem boundedMultiplicity_exists_shared_overload_vertex
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexpLt : ∀ x, exponent x < n)
    (hexp : ∀ x, exponent x ≤ n)
    (honeLoss :
      ∀ x, (active C x).card ≤ n - exponent x + 1)
    {T : Finset V}
    (hdef :
      BlockDeficient
        (fun x => 2 ^ exponent x)
        (enlargedProjectedCandidateBlock C exponent)
        T)
    (hle :
      ∀ word : Fin n → Bool,
        (coreEnlargedCandidateFibre C exponent T word).card ≤ 2) :
    ∃ v ∈ T,
      2 *
        ((enlargedProjectedCandidateBlock C exponent v).card -
          2 ^ exponent v)
        <
      (sharedBlockWords
        (enlargedProjectedCandidateBlock C exponent)
        T v).card := by
  classical
  by_contra hnone
  push_neg at hnone
  have hsumLe :
      (∑ v ∈ T,
        (sharedBlockWords
          (enlargedProjectedCandidateBlock C exponent)
          T v).card)
        ≤
      2 *
        (∑ v ∈ T,
          ((enlargedProjectedCandidateBlock C exponent v).card -
            2 ^ exponent v)) := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun v hv => hnone v hv
  have heq :=
    boundedMultiplicity_sum_shared_eq_two_slack_add_two_deficiency
      C exponent hexpLt hexp honeLoss hdef hle
  have hpos :=
    blockDeficiencyAmount_pos_of_deficient
      (fun x : V => 2 ^ exponent x)
      (enlargedProjectedCandidateBlock C exponent)
      hdef
  omega

theorem deficientCore_tripleFibre_or_exactTopLossOverload
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexpLt : ∀ x, exponent x < n)
    (hexp : ∀ x, exponent x ≤ n)
    (honeLoss :
      ∀ x, (active C x).card ≤ n - exponent x + 1)
    {T : Finset V}
    (hdef :
      BlockDeficient
        (fun x => 2 ^ exponent x)
        (enlargedProjectedCandidateBlock C exponent)
        T) :
    (
      ∃ word : Fin n → Bool,
        3 ≤ (coreEnlargedCandidateFibre
          C exponent T word).card
    )
    ∨
    (
      ∃ v ∈ T,
        (
          ExactProjectedBudget C exponent v
          ∨
          (v ∈ projectedLossVertices C exponent ∧
            exponent v = n - 1)
        )
        ∧
        2 *
          ((enlargedProjectedCandidateBlock C exponent v).card -
            2 ^ exponent v)
          <
        (sharedBlockWords
          (enlargedProjectedCandidateBlock C exponent)
          T v).card
    ) := by
  classical
  by_cases hle :
      ∀ word : Fin n → Bool,
        (coreEnlargedCandidateFibre C exponent T word).card ≤ 2
  · right
    obtain ⟨v,hvT,hover⟩ :=
      boundedMultiplicity_exists_shared_overload_vertex
        C exponent hexpLt hexp honeLoss hdef hle
    exact ⟨v,hvT,
      longCycle_shared_overload_exact_or_topLoss
        C exponent hexpLt hexp honeLoss hvT hover,
      hover⟩
  · left
    push_neg at hle
    obtain ⟨word,hword⟩ := hle
    exact ⟨word,by omega⟩

#print axioms coreEnlargedCandidateFibre_card_eq_two_of_shared_of_card_le_two
#print axioms boundedMultiplicity_sum_shared_cards_eq_two_mul_doubleCovered
#print axioms boundedMultiplicity_doubleCovered_eq_totalSlack_add_deficiency
#print axioms boundedMultiplicity_exists_shared_overload_vertex
#print axioms deficientCore_tripleFibre_or_exactTopLossOverload


/-- Under the fibre-multiplicity bound, the shared-mass overload already
produces the same recursive data previously extracted only in the long-cycle
branch: either an exact shared outlet, or a top-loss retained completion word
which is shared with another candidate block. -/
theorem boundedMultiplicity_overload_recursive_outlet
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexpLt : ∀ x, exponent x < n)
    (hexp : ∀ x, exponent x ≤ n)
    (honeLoss :
      ∀ x, (active C x).card ≤ n - exponent x + 1)
    {T : Finset V}
    (hdef :
      BlockDeficient
        (fun x => 2 ^ exponent x)
        (enlargedProjectedCandidateBlock C exponent)
        T)
    (hle :
      ∀ word : Fin n → Bool,
        (coreEnlargedCandidateFibre C exponent T word).card ≤ 2) :
    (
      ∃ v ∈ T,
        ExactProjectedBudget C exponent v ∧
        ExactSharedOutlet C exponent v
    )
    ∨
    (
      ∃ v ∈ T,
        v ∈ projectedLossVertices C exponent ∧
        exponent v = n - 1 ∧
        (
          sharedBlockWords
            (enlargedProjectedCandidateBlock C exponent)
            T v
          ∩
          retainedCompletionWords C v
        ).Nonempty
    ) := by
  obtain ⟨v,hvT,hover⟩ :=
    boundedMultiplicity_exists_shared_overload_vertex
      C exponent hexpLt hexp honeLoss hdef hle
  rcases
    longCycle_shared_overload_exact_or_topLoss
      C exponent hexpLt hexp honeLoss hvT hover
    with hvExact | ⟨hvLoss,hvTop⟩
  · exact Or.inl
      ⟨v,hvT,hvExact,
        longCycle_exact_overload_has_shared_outlet
          C exponent hexp honeLoss hvT hvExact hover⟩
  · exact Or.inr
      ⟨v,hvT,hvLoss,hvTop,
        topLoss_overload_has_shared_completion_word
          C exponent hvLoss hvTop hover⟩

/-- Girth-free recursive root: a deficient core either contains a
triple-covered Boolean word, or already has an exact shared outlet / top-loss
shared completion word. -/
theorem deficientCore_tripleFibre_or_recursiveOverload
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexpLt : ∀ x, exponent x < n)
    (hexp : ∀ x, exponent x ≤ n)
    (honeLoss :
      ∀ x, (active C x).card ≤ n - exponent x + 1)
    {T : Finset V}
    (hdef :
      BlockDeficient
        (fun x => 2 ^ exponent x)
        (enlargedProjectedCandidateBlock C exponent)
        T) :
    (
      ∃ word : Fin n → Bool,
        3 ≤ (coreEnlargedCandidateFibre
          C exponent T word).card
    )
    ∨
    (
      ∃ v ∈ T,
        ExactProjectedBudget C exponent v ∧
        ExactSharedOutlet C exponent v
    )
    ∨
    (
      ∃ v ∈ T,
        v ∈ projectedLossVertices C exponent ∧
        exponent v = n - 1 ∧
        (
          sharedBlockWords
            (enlargedProjectedCandidateBlock C exponent)
            T v
          ∩
          retainedCompletionWords C v
        ).Nonempty
    ) := by
  classical
  by_cases hle :
      ∀ word : Fin n → Bool,
        (coreEnlargedCandidateFibre C exponent T word).card ≤ 2
  · rcases
      boundedMultiplicity_overload_recursive_outlet
        C exponent hexpLt hexp honeLoss hdef hle
      with hexact | htop
    · exact Or.inr (Or.inl hexact)
    · exact Or.inr (Or.inr htop)
  · left
    push_neg at hle
    obtain ⟨word,hword⟩ := hle
    exact ⟨word,by omega⟩

#print axioms boundedMultiplicity_overload_recursive_outlet
#print axioms deficientCore_tripleFibre_or_recursiveOverload

end OrderedEdgeColoring
end JSP000404Research
