
import JSP000404Research.ResidualCompletionMultiplicity
import JSP000404Research.ResidualProjectionAccounting
import Mathlib.Tactic

/-!
# Exact overlap accounting for retained completion cubes

For every retained Boolean word x define its completion fibre

  F(x) = {v | x belongs to the retained completion cube Q_v}.

ResidualCompletionMultiplicity proves conceptually that no word can belong to
three different Q_v.  Here we package this more sharply: the residual canonical
bit gives an injection

  F(x) -> Bool.

Hence card F(x) <= 2.

Define

  coveredWords = {x | card F(x) >= 1},
  overlapWords = {x | card F(x) = 2}.

Because each multiplicity is 0,1,or 2,

  card F(x)
    = 1_{coveredWords}(x) + 1_{overlapWords}(x).

Double-counting incidences (v,x) with x in Q_v therefore gives

  sum_v card(Q_v)
    = card(coveredWords) + card(overlapWords).

Since card(Q_v)=2^(n-card(retainedActive(v))), this is exactly the projected
mass decomposition required by ResidualProjectionAccounting.
-/

namespace JSP000404Research
namespace OrderedEdgeColoring

open scoped BigOperators

noncomputable def completionFibre
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (word : Fin n → Bool) : Finset V := by
  classical
  exact Finset.univ.filter fun v =>
    word ∈ retainedCompletionWords C v

@[simp] theorem mem_completionFibre
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (word : Fin n → Bool) (v : V) :
    v ∈ completionFibre C word ↔
      word ∈ retainedCompletionWords C v := by
  classical
  simp [completionFibre]

/-- The residual bit distinguishes the at-most-two vertices whose retained
completion cubes contain one fixed retained word. -/
theorem completionFibre_card_le_two
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (word : Fin n → Bool) :
    (completionFibre C word).card ≤ 2 := by
  classical
  let f :
      {v : V // v ∈ completionFibre C word} → Bool :=
    fun v => bit C v.1 (residualCoord n)
  have hf : Function.Injective f := by
    intro u v huvBit
    apply Subtype.ext
    by_contra huv
    have huWord :
        word ∈ retainedCompletionWords C u.1 := by
      exact (mem_completionFibre C word u.1).1 u.2
    have hvWord :
        word ∈ retainedCompletionWords C v.1 := by
      exact (mem_completionFibre C word v.1).1 v.2
    rcases retainedCompletion_overlap_forces_residual
        C huv huWord hvWord with hres | hres
    · have hcol :
          C.color u.1 v.1 = residualCoord n := by
        apply Fin.ext
        simpa [residualCoord] using
          residual_val_eq C hres.2
      have hne := edgeColor_bit_ne C hres.1
      rw [hcol] at hne
      exact hne huvBit
    · have hcol :
          C.color v.1 u.1 = residualCoord n := by
        apply Fin.ext
        simpa [residualCoord] using
          residual_val_eq C hres.2
      have hne := edgeColor_bit_ne C hres.1
      rw [hcol] at hne
      exact hne huvBit.symm
  have hcard :=
    Fintype.card_le_of_injective f hf
  simpa [f] using hcard

noncomputable def coveredCompletionWords
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1)) :
    Finset (Fin n → Bool) := by
  classical
  exact Finset.univ.filter fun word =>
    (completionFibre C word).Nonempty

noncomputable def overlapCompletionWords
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1)) :
    Finset (Fin n → Bool) := by
  classical
  exact Finset.univ.filter fun word =>
    (completionFibre C word).card = 2

@[simp] theorem mem_coveredCompletionWords
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (word : Fin n → Bool) :
    word ∈ coveredCompletionWords C ↔
      (completionFibre C word).Nonempty := by
  classical
  simp [coveredCompletionWords]

@[simp] theorem mem_overlapCompletionWords
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (word : Fin n → Bool) :
    word ∈ overlapCompletionWords C ↔
      (completionFibre C word).card = 2 := by
  classical
  simp [overlapCompletionWords]

/-- Pointwise 0/1/2 multiplicity decomposition. -/
theorem completionFibre_card_eq_covered_indicator_add_overlap_indicator
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (word : Fin n → Bool) :
    (completionFibre C word).card =
      (if word ∈ coveredCompletionWords C then 1 else 0) +
      (if word ∈ overlapCompletionWords C then 1 else 0) := by
  classical
  have hle := completionFibre_card_le_two C word
  by_cases hpos : (completionFibre C word).Nonempty
  · have hcardPos : 0 < (completionFibre C word).card :=
      Finset.card_pos.mpr hpos
    by_cases htwo : (completionFibre C word).card = 2
    · simp [hpos, htwo]
    · have hone : (completionFibre C word).card = 1 := by
        omega
      simp [hpos, htwo, hone]
  · have hzero :
        (completionFibre C word).card = 0 :=
      Finset.not_nonempty_iff_eq_empty.mp hpos |>
        congrArg Finset.card |>
        (by simpa using ·)
    simp [hpos, hzero]

/-- Incidence type indexed first by vertices. -/
abbrev CompletionIncidenceByVertex
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1)) :=
  Σ v : V, {word : Fin n → Bool //
    word ∈ retainedCompletionWords C v}

/-- The same incidences indexed first by retained words. -/
abbrev CompletionIncidenceByWord
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1)) :=
  Σ word : Fin n → Bool, {v : V //
    v ∈ completionFibre C word}

noncomputable def completionIncidenceSwap
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1)) :
    CompletionIncidenceByVertex C ≃
      CompletionIncidenceByWord C where
  toFun x := ⟨x.2.1, ⟨x.1, by
    exact (mem_completionFibre C x.2.1 x.1).2 x.2.2⟩⟩
  invFun x := ⟨x.2.1, ⟨x.1, by
    exact (mem_completionFibre C x.1 x.2.1).1 x.2.2⟩⟩
  left_inv x := by
    cases x with
    | mk v word =>
        cases word
        rfl
  right_inv x := by
    cases x with
    | mk word v =>
        cases v
        rfl

/-- Double-counting the same finite incidence relation. -/
theorem sum_retainedCompletionWords_card_eq_sum_completionFibre_card
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1)) :
    (∑ v, (retainedCompletionWords C v).card) =
      ∑ word, (completionFibre C word).card := by
  classical
  have hcard :=
    Fintype.card_congr (completionIncidenceSwap C)
  simpa [CompletionIncidenceByVertex,
    CompletionIncidenceByWord,
    Fintype.card_sigma] using hcard

/-- Multiplicity <=2 turns the incidence sum into union plus overlap count. -/
theorem sum_completionFibre_card_eq_covered_add_overlap
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1)) :
    (∑ word, (completionFibre C word).card) =
      (coveredCompletionWords C).card +
        (overlapCompletionWords C).card := by
  classical
  calc
    (∑ word, (completionFibre C word).card)
        =
      ∑ word,
        ((if word ∈ coveredCompletionWords C then 1 else 0) +
         (if word ∈ overlapCompletionWords C then 1 else 0)) := by
          apply Finset.sum_congr rfl
          intro word _
          exact
            completionFibre_card_eq_covered_indicator_add_overlap_indicator
              C word
    _ =
      (∑ word,
        if word ∈ coveredCompletionWords C then 1 else 0) +
      (∑ word,
        if word ∈ overlapCompletionWords C then 1 else 0) := by
          rw [Finset.sum_add_distrib]
    _ =
      (coveredCompletionWords C).card +
        (overlapCompletionWords C).card := by
          simp

/-- Exact retained projected-mass decomposition. -/
theorem projectedFree_mass_eq_covered_add_overlap
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1)) :
    (∑ v, 2 ^ (n - (retainedActive C v).card)) =
      (coveredCompletionWords C).card +
        (overlapCompletionWords C).card := by
  calc
    (∑ v, 2 ^ (n - (retainedActive C v).card))
        =
      ∑ v, (retainedCompletionWords C v).card := by
          apply Finset.sum_congr rfl
          intro v _
          symm
          exact retainedCompletionWords_card C v
    _ = ∑ word, (completionFibre C word).card :=
      sum_retainedCompletionWords_card_eq_sum_completionFibre_card C
    _ =
      (coveredCompletionWords C).card +
        (overlapCompletionWords C).card :=
      sum_completionFibre_card_eq_covered_add_overlap C

/-- The covered retained words are a subset of the ambient n-cube. -/
theorem coveredCompletionWords_card_le_two_pow
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1)) :
    (coveredCompletionWords C).card ≤ 2 ^ n := by
  have hle :
      (coveredCompletionWords C).card ≤
        Fintype.card (Fin n → Bool) := by
    simpa using Finset.card_le_univ (coveredCompletionWords C)
  simpa [Fintype.card_fun] using hle

/-- Final residual-projection outlet in exact completion-set language. -/
theorem exponent_capacity_of_completion_defect_payment
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hpay :
      (overlapCompletionWords C).card +
          totalDyadicProfileLoss exponent
            (fun v => n - (retainedActive C v).card)
        ≤
      (2 ^ n - (coveredCompletionWords C).card) +
          totalDyadicProfileSurplus exponent
            (fun v => n - (retainedActive C v).card)) :
    (∑ v, 2 ^ exponent v) ≤ 2 ^ n := by
  exact dyadic_capacity_of_residual_projection_accounting
    exponent
    (fun v => n - (retainedActive C v).card)
    n
    (coveredCompletionWords C).card
    (overlapCompletionWords C).card
    (coveredCompletionWords_card_le_two_pow C)
    (projectedFree_mass_eq_covered_add_overlap C)
    hpay

#print axioms completionFibre_card_le_two
#print axioms sum_retainedCompletionWords_card_eq_sum_completionFibre_card
#print axioms sum_completionFibre_card_eq_covered_add_overlap
#print axioms projectedFree_mass_eq_covered_add_overlap
#print axioms exponent_capacity_of_completion_defect_payment

end OrderedEdgeColoring
end JSP000404Research
