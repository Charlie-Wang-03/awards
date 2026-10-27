import JSP000404Research.ActualEightSourceUnitDeficitReduction
import Mathlib.Tactic

/-!
# Minimal Hall deficits have fully shadowed genuine source credits

An arbitrary failure of a finite family of source-to-credit eligibility
sets has an INCLUSION-MINIMAL deficient finite source core. For that
core T:

* exactly ONE genuine credit is missing: |N(T)| + 1 = |T|;
* every STRICT subfamily U of T satisfies Hall;
* deleting ANY single original source x in T does not lose a single
  distinct eligible credit: N(T.erase x) = N(T).

Thus proving nonexistence of these fully shadowed, single-credit,
inclusion-minimal obstructions is sufficient for the complete eight-lane
original non-reusing payment. Nothing here manufactures a true
Boolean hole or an available profile surplus unit, and no geometric
AngleCap expansion assumption is inserted.
-/

namespace JSP000404Research
namespace OrderedEdgeColoring

/-- Any failed Hall inequality admits an inclusion-minimal deficient
subfamily with *exactly* one missing credit. Every strict smaller
subfamily satisfies the literal unchanged eligible-credit Hall bound. -/
theorem finite_hall_failure_contains_minimal_unit_deficit
    {α β : Type*} [DecidableEq α] [DecidableEq β]
    (eligible : α → Finset β)
    (S : Finset α)
    (hbad : (S.biUnion eligible).card < S.card) :
    ∃ T : Finset α,
      T ⊆ S ∧
      (T.biUnion eligible).card + 1 = T.card ∧
      (∀ U : Finset α, U ⊂ T →
        U.card ≤ (U.biUnion eligible).card) := by
  classical
  have hStrong :
      ∀ k : ℕ, ∀ A : Finset α, A.card = k →
        (A.biUnion eligible).card < A.card →
        ∃ T : Finset α,
          T ⊆ A ∧
          (T.biUnion eligible).card + 1 = T.card ∧
          (∀ U : Finset α, U ⊂ T →
            U.card ≤ (U.biUnion eligible).card) := by
    intro k
    induction k using Nat.strong_induction_on with
    | h k ih =>
      intro A hk hFail
      by_cases hProper :
          ∃ U : Finset α, U ⊂ A ∧
            (U.biUnion eligible).card < U.card
      · obtain ⟨U, hUA, hUFail⟩ := hProper
        have hsmaller : U.card < k := by
          rw [← hk]
          exact Finset.card_lt_card hUA
        obtain ⟨T, hTU, hUnit, hCritical⟩ :=
          ih U.card hsmaller U rfl hUFail
        exact ⟨T, hTU.trans hUA.subset, hUnit, hCritical⟩
      · have hCritical :
            ∀ U : Finset α, U ⊂ A →
              U.card ≤ (U.biUnion eligible).card := by
          intro U hUA
          exact Nat.le_of_not_gt (by
            intro hFailU
            exact hProper ⟨U, hUA, hFailU⟩)
        have hPos : 0 < A.card := by omega
        obtain ⟨a, ha⟩ := Finset.card_pos.mp hPos
        have hDel : A.erase a ⊂ A := Finset.erase_ssubset ha
        have hHallDel := hCritical (A.erase a) hDel
        have hNeighMono :
            ((A.erase a).biUnion eligible).card ≤
              (A.biUnion eligible).card := by
          apply Finset.card_le_card
          intro b hb
          obtain ⟨i, hi, hbi⟩ := Finset.mem_biUnion.mp hb
          exact Finset.mem_biUnion.mpr
            ⟨i, (Finset.mem_erase.mp hi).2, hbi⟩
        have hCardDel : (A.erase a).card + 1 = A.card := by
          simp only [Finset.card_erase_of_mem ha]
          omega
        refine ⟨A, Finset.Subset.rfl, ?_, hCritical⟩
        omega
  exact hStrong S.card S rfl hbad

/-- An inclusion-minimal single-credit deficit is a total source
shadow: removing any source leaves the entire union of distinct
genuinely eligible credit tokens literally unchanged. -/
theorem minimal_hall_unit_deficit_all_sources_shadowed
    {α β : Type*} [DecidableEq α] [DecidableEq β]
    (eligible : α → Finset β)
    (T : Finset α)
    (hUnit : (T.biUnion eligible).card + 1 = T.card)
    (hCritical : ∀ U : Finset α, U ⊂ T →
        U.card ≤ (U.biUnion eligible).card) :
    ∀ a ∈ T,
      (T.erase a).biUnion eligible = T.biUnion eligible := by
  intro a ha
  have hSubset :
      (T.erase a).biUnion eligible ⊆ T.biUnion eligible := by
    intro b hb
    obtain ⟨i, hi, hbi⟩ := Finset.mem_biUnion.mp hb
    exact Finset.mem_biUnion.mpr
      ⟨i, (Finset.mem_erase.mp hi).2, hbi⟩
  have hLe := Finset.card_le_card hSubset
  have hHallErase :=
    hCritical (T.erase a) (Finset.erase_ssubset ha)
  have hSize : (T.erase a).card + 1 = T.card := by
    simp only [Finset.card_erase_of_mem ha]
    omega
  have hEqCard :
      (T.biUnion eligible).card =
        ((T.erase a).biUnion eligible).card := by omega
  exact Finset.eq_of_subset_of_card_le hSubset (by omega)

/-- For EVERY given fully source-native ACTUAL eight-class ledger and
eligibility map into the only two legal global credit classes,
either Hall holds or the failure is witnessed by a critical finite
original debt subfamily with a precise one-credit deficit and
complete credit-shadowing for every debt source. -/
theorem actual_eight_earliest_hall_or_minimal_shadow_deficit
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (B : OrderedEdgeColoring V (n + 1))
    (k : V → ℕ) (choice : V → Fin n)
    (eligible :
      actualEightSourceEarliestDebtTokens B k choice →
        Finset (actualExternalPaymentCredits B k choice)) :
    letI : DecidableEq (actualEightSourceEarliestDebtTokens B k choice) :=
      Classical.decEq _
    (∀ S : Finset (actualEightSourceEarliestDebtTokens B k choice),
      S.card ≤ (S.biUnion eligible).card) ∨
    (∃ T : Finset (actualEightSourceEarliestDebtTokens B k choice),
      (T.biUnion eligible).card + 1 = T.card ∧
      (∀ U : Finset (actualEightSourceEarliestDebtTokens B k choice),
        U ⊂ T → U.card ≤ (U.biUnion eligible).card) ∧
      (∀ a ∈ T,
        (T.erase a).biUnion eligible = T.biUnion eligible)) := by
  classical
  by_cases hHall :
      ∀ S : Finset (actualEightSourceEarliestDebtTokens B k choice),
        S.card ≤ (S.biUnion eligible).card
  · exact Or.inl hHall
  · right
    have hFailure :
        ∃ S : Finset (actualEightSourceEarliestDebtTokens B k choice),
          (S.biUnion eligible).card < S.card := by
      by_contra h
      apply hHall
      intro S
      by_contra hSmaller
      apply h
      exact ⟨S, by omega⟩
    obtain ⟨S, hS⟩ := hFailure
    obtain ⟨T, _hTS, hUnit, hCrit⟩ :=
      finite_hall_failure_contains_minimal_unit_deficit eligible S hS
    exact ⟨T, hUnit, hCrit,
      minimal_hall_unit_deficit_all_sources_shadowed
        eligible T hUnit hCrit⟩


/-- Each genuinely eligible payment credit in an inclusion-minimal
one-credit Hall-deficient core is offered to at least TWO DISTINCT
source tokens inside that core. This upgrades equality of shadowed
neighbourhood unions to source-native credit-reuse witnesses. -/
theorem minimal_hall_unit_deficit_all_credits_double_claimed
    {α β : Type*} [DecidableEq α] [DecidableEq β]
    (eligible : α → Finset β)
    (T : Finset α)
    (hUnit : (T.biUnion eligible).card + 1 = T.card)
    (hCritical : ∀ U : Finset α, U ⊂ T →
        U.card ≤ (U.biUnion eligible).card) :
    ∀ c ∈ T.biUnion eligible,
      ∃ a b : α,
        a ∈ T ∧ b ∈ T ∧ a ≠ b ∧
        c ∈ eligible a ∧ c ∈ eligible b := by
  intro c hc
  obtain ⟨a, ha, hca⟩ := Finset.mem_biUnion.mp hc
  have hShadow :=
    minimal_hall_unit_deficit_all_sources_shadowed
      eligible T hUnit hCritical a ha
  have hcErase : c ∈ (T.erase a).biUnion eligible := by
    rw [hShadow]
    exact hc
  obtain ⟨b, hbErase, hcb⟩ := Finset.mem_biUnion.mp hcErase
  have hb : b ∈ T := (Finset.mem_erase.mp hbErase).2
  have hab : a ≠ b := (Finset.mem_erase.mp hbErase).1.symm
  exact ⟨a, b, ha, hb, hab, hca, hcb⟩

/-- The ACTUAL earliest-prior eight-lane debt ledger:
a failed source-to-real-credit Hall relation exhibits one critical
one-credit deficit T in which EVERY candidate TRUE-hole or actually
unreserved-surplus credit is claimed by TWO DISTINCT genuine source
tokens. Both source memberships are original, not anonymous Fin
debts; every eligible credit remains one of the two legally usable
global payment types.

No universal AngleCap exclusion of this necessary double-claim
motif is asserted. -/
theorem actual_eight_earliest_failed_hall_has_double_claimed_credit_core
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (B : OrderedEdgeColoring V (n + 1))
    (k : V → ℕ) (choice : V → Fin n)
    (eligible :
      actualEightSourceEarliestDebtTokens B k choice →
        Finset (actualExternalPaymentCredits B k choice))
    (hFail :
      ∃ S : Finset (actualEightSourceEarliestDebtTokens B k choice),
        (S.biUnion eligible).card < S.card) :
    ∃ T : Finset (actualEightSourceEarliestDebtTokens B k choice),
      (T.biUnion eligible).card + 1 = T.card ∧
      (∀ c ∈ T.biUnion eligible,
        ∃ a b : actualEightSourceEarliestDebtTokens B k choice,
          a ∈ T ∧ b ∈ T ∧ a ≠ b ∧
          c ∈ eligible a ∧ c ∈ eligible b) := by
  classical
  obtain ⟨S, hS⟩ := hFail
  obtain ⟨T, _hTS, hUnit, hCritical⟩ :=
    finite_hall_failure_contains_minimal_unit_deficit
      eligible S hS
  exact ⟨T, hUnit,
    minimal_hall_unit_deficit_all_credits_double_claimed
      eligible T hUnit hCritical⟩

#print axioms minimal_hall_unit_deficit_all_credits_double_claimed
#print axioms actual_eight_earliest_failed_hall_has_double_claimed_credit_core

#print axioms finite_hall_failure_contains_minimal_unit_deficit
#print axioms minimal_hall_unit_deficit_all_sources_shadowed
#print axioms actual_eight_earliest_hall_or_minimal_shadow_deficit


/-- Hall-critical one-credit cores admit a LEGAL injective matching
after deleting ANY chosen source token.  The matching is constructed
over the actual dependent subtype of remaining sources, so it neither
requires fictional extra source slots nor pays the deleted token.

This is strictly stronger than neighbourhood shadowing: the other
sources can in fact be assigned DISTINCT legal credits. -/
theorem minimal_hall_unit_deficit_erase_has_injective_payment
    {α β : Type*} [DecidableEq α] [DecidableEq β]
    (eligible : α → Finset β)
    (T : Finset α)
    (hUnit : (T.biUnion eligible).card + 1 = T.card)
    (hCritical : ∀ U : Finset α, U ⊂ T →
      U.card ≤ (U.biUnion eligible).card) :
    ∀ a ∈ T,
      ∃ f : {x : α // x ∈ T.erase a} → β,
        Function.Injective f ∧
        ∀ x, f x ∈ eligible x.1 := by
  classical
  intro a ha
  let E : {x : α // x ∈ T.erase a} → Finset β :=
    fun x => eligible x.1
  have hHall :
      ∀ S : Finset {x : α // x ∈ T.erase a},
        S.card ≤ (S.biUnion E).card := by
    intro S
    let emb : {x : α // x ∈ T.erase a} ↪ α :=
      ⟨Subtype.val, by
        intro x y h
        exact Subtype.ext h⟩
    let U : Finset α := S.map emb
    have hUdel : U ⊆ T.erase a := by
      intro x hx
      obtain ⟨v, hv, rfl⟩ := Finset.mem_map.mp hx
      exact v.property
    have hUcrit : U ⊂ T :=
      ssubset_of_subset_of_ssubset hUdel (Finset.erase_ssubset ha)
    have hBase := hCritical U hUcrit
    have hCard : U.card = S.card := by
      simp [U]
    have hNeigh : U.biUnion eligible = S.biUnion E := by
      ext b
      constructor
      · intro hb
        obtain ⟨x, hx, hbx⟩ := Finset.mem_biUnion.mp hb
        obtain ⟨v, hv, rfl⟩ := Finset.mem_map.mp hx
        exact Finset.mem_biUnion.mpr ⟨v, hv, hbx⟩
      · intro hb
        obtain ⟨v, hv, hbv⟩ := Finset.mem_biUnion.mp hb
        exact Finset.mem_biUnion.mpr
          ⟨emb v, Finset.mem_map.mpr ⟨v, hv, rfl⟩, hbv⟩
    calc
      S.card = U.card := hCard.symm
      _ ≤ (U.biUnion eligible).card := hBase
      _ = (S.biUnion E).card := congrArg Finset.card hNeigh
  obtain ⟨f, hinj, hlegal⟩ :=
    (Finset.all_card_le_biUnion_card_iff_exists_injective E).mp hHall
  exact ⟨f, hinj, hlegal⟩

/-- Source-native ACTUAL eight-class version: if the selected true-hole
and unreserved-surplus eligibility relation has an inclusion-minimal
one-credit Hall deficit, then removing ANY genuine original debt
token leaves a fully NONREUSING legal payment for all other tokens.

It does NOT pay the deleted source, establish universal AngleCap
expansion, or remove the genuine global WIP sorry. -/
theorem actual_eight_earliest_critical_core_each_source_deletable
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (B : OrderedEdgeColoring V (n + 1))
    (k : V → ℕ) (choice : V → Fin n)
    (eligible :
      actualEightSourceEarliestDebtTokens B k choice →
        Finset (actualExternalPaymentCredits B k choice))
    (T : Finset (actualEightSourceEarliestDebtTokens B k choice))
    (hUnit : (T.biUnion eligible).card + 1 = T.card)
    (hCritical :
      ∀ U : Finset (actualEightSourceEarliestDebtTokens B k choice),
        U ⊂ T → U.card ≤ (U.biUnion eligible).card) :
    ∀ a ∈ T,
      ∃ f : {x : actualEightSourceEarliestDebtTokens B k choice //
                x ∈ T.erase a} →
          actualExternalPaymentCredits B k choice,
        Function.Injective f ∧
        ∀ x, f x ∈ eligible x.1 := by
  classical
  exact minimal_hall_unit_deficit_erase_has_injective_payment
    eligible T hUnit hCritical

#print axioms minimal_hall_unit_deficit_erase_has_injective_payment
#print axioms actual_eight_earliest_critical_core_each_source_deletable

end OrderedEdgeColoring
end JSP000404Research
