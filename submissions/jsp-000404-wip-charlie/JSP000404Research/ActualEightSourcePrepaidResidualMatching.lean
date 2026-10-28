import JSP000404Research.ActualEighthTokenLocalPrepayment
import JSP000404Research.ActualEightSourceEarliestDebtPayment
import Mathlib.Tactic

/-!
# Complete original eight-source matching after source-native eighth prepayment

The ORIGINAL eight-lane debt type uses seven genuine terminal/covered
source families, plus the dependent earliest-prior collision tokens
in its final eighth summand.

We first select exactly one real dependent eighth token per genuine
locally eligible outside-translated true-hole credit. We embed the
selection into the ORIGINAL eight-lane source type, not a surrogate.
The selected credits are actually used once and removed from the
remaining genuine global credit supply.

An independently established injection of ALL REMAINING real eight-
lane sources into ONLY credits outside that prepaid image can then
be glued to the existing local injection without reuse. This is
a precise reduced target for the ORIGINAL global AngleCap theorem:
NO such residual injection is claimed to exist unconditionally.
-/

namespace JSP000404Research
namespace OrderedEdgeColoring

/-- Generic finite credit matching can be completed without double use:
a paid source subset, matched injectively, and an injection from all
unpaid sources to the *complement of the already spent credits* give
a single injective allocation of all original sources. -/
theorem finite_prepaid_and_remaining_matching_glue
    {α β : Type*} [DecidableEq α] [DecidableEq β]
    (P : Finset α)
    (prepay : {x : α // x ∈ P} → β)
    (hprepay : Function.Injective prepay)
    (remaining : {x : α // x ∉ P} →
      {y : β // y ∉ (Finset.univ : Finset {x : α // x ∈ P}).image prepay})
    (hremaining : Function.Injective remaining) :
    ∃ whole : α → β, Function.Injective whole := by
  classical
  let L : Finset β :=
    (Finset.univ : Finset {x : α // x ∈ P}).image prepay
  let whole (x : α) : β :=
    if h : x ∈ P then prepay ⟨x, h⟩ else (remaining ⟨x, h⟩).1
  refine ⟨whole, ?_⟩
  intro x y hxy
  by_cases hx : x ∈ P
  · by_cases hy : y ∈ P
    · have heq : prepay ⟨x, hx⟩ = prepay ⟨y, hy⟩ := by
        simpa only [whole, dif_pos hx, dif_pos hy] using hxy
      have hsub := hprepay heq
      exact congrArg Subtype.val hsub
    · have hxL : whole x ∈ L := by
        change (if h : x ∈ P then prepay ⟨x, h⟩
          else (remaining ⟨x, h⟩).1) ∈ L
        rw [dif_pos hx]
        exact Finset.mem_image.mpr
          ⟨⟨x, hx⟩, Finset.mem_univ _, rfl⟩
      have hyNotL : whole y ∉ L := by
        simpa only [whole, dif_neg hy] using (remaining ⟨y, hy⟩).2
      exact False.elim (hyNotL (hxy ▸ hxL))
  · by_cases hy : y ∈ P
    · have hyL : whole y ∈ L := by
        change (if h : y ∈ P then prepay ⟨y, h⟩
          else (remaining ⟨y, h⟩).1) ∈ L
        rw [dif_pos hy]
        exact Finset.mem_image.mpr
          ⟨⟨y, hy⟩, Finset.mem_univ _, rfl⟩
      have hxNotL : whole x ∉ L := by
        simpa only [whole, dif_neg hx] using (remaining ⟨x, hx⟩).2
      exact False.elim (hxNotL (hxy.symm ▸ hyL))
    · have heq : remaining ⟨x, hx⟩ = remaining ⟨y, hy⟩ := by
        apply Subtype.ext
        simpa only [whole, dif_neg hx, dif_neg hy] using hxy
      exact congrArg Subtype.val (hremaining heq)

/-- The genuine dependent eighth debt token enters the ACTUAL
eight-source family in the last, eighth, disjoint-sum branch. -/
def actual_eighth_token_as_full_source
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ) (choice : V → Fin n)
    (x : actualEarliestLossDebtTokenType C exponent choice) :
    actualEightSourceEarliestDebtTokens C exponent choice :=
  Sum.inr (Sum.inr (Sum.inr (Sum.inr
    (Sum.inr (Sum.inr (Sum.inr x))))))

/-- Embedding a genuine dependent eighth token into the tagged
eight-source type never merges it with any other eighth token. -/
theorem actual_eighth_token_as_full_source_injective
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ) (choice : V → Fin n) :
    Function.Injective
      (actual_eighth_token_as_full_source C exponent choice) := by
  intro x y hxy
  simpa only [actual_eighth_token_as_full_source, Sum.inr.injEq] using hxy

/-- A genuine LOCAL prepaid subset of the COMPLETE ORIGINAL eight-
source family always exists. Each selected full-source token is
actually an eighth dependent collision token; all other seven classes
are untouched. Its legitimate global credit allocation is injective
and belongs to the TRUE-hole (not surplus) branch. -/
theorem actual_eight_original_genuine_eighth_prepayment_exists
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ) (choice : V → Fin n) :
    ∃ P : Finset (actualEightSourceEarliestDebtTokens C exponent choice),
      (∀ d ∈ P, ∃ x : actualEarliestLossDebtTokenType C exponent choice,
        d = actual_eighth_token_as_full_source C exponent choice x) ∧
      ∃ prepay : {d : actualEightSourceEarliestDebtTokens C exponent choice //
          d ∈ P} → actualExternalPaymentCredits C exponent choice,
        Function.Injective prepay ∧
        (∀ d, ∃ q : {q : Fin n → Bool //
          q ∈ lossLedgerOutsideTranslatedTrueHoles C exponent choice},
          prepay d = Sum.inl q) := by
  classical
  obtain ⟨T, _hsub, _himage, local, hlocalinj, hlocalreal⟩ :=
    actual_eighth_allwidth_dependent_tokens_local_credit_injection
      C exponent choice
  let e := actualEarliestLossDebtEquivCollisionRecord C exponent choice
  let E := {x : actualEarliestLossDebtTokenType C exponent choice //
    (e x).1 ∈ T}
  let tag : E → actualEightSourceEarliestDebtTokens C exponent choice :=
    fun x => actual_eighth_token_as_full_source C exponent choice x.1
  let P : Finset (actualEightSourceEarliestDebtTokens C exponent choice) :=
    (Finset.univ : Finset E).image tag
  have htrueSource : ∀ d ∈ P,
      ∃ x : actualEarliestLossDebtTokenType C exponent choice,
        d = actual_eighth_token_as_full_source C exponent choice x := by
    intro d hd
    obtain ⟨x, _, hxd⟩ := Finset.mem_image.mp hd
    exact ⟨x.1, hxd.symm⟩
  have hsource (d : {d : actualEightSourceEarliestDebtTokens C exponent choice //
      d ∈ P}) : ∃ x : E, tag x = d.1 := by
    exact Finset.mem_image.mp d.2
  let choose (d : {d : actualEightSourceEarliestDebtTokens C exponent choice //
      d ∈ P}) : E := Classical.choose (hsource d)
  have hchoose (d : {d : actualEightSourceEarliestDebtTokens C exponent choice //
      d ∈ P}) : tag (choose d) = d.1 := Classical.choose_spec (hsource d)
  let prepay (d : {d : actualEightSourceEarliestDebtTokens C exponent choice //
      d ∈ P}) : actualExternalPaymentCredits C exponent choice :=
    local (choose d)
  have hpreinj : Function.Injective prepay := by
    intro a b hab
    have hab' : choose a = choose b := hlocalinj hab
    apply Subtype.ext
    calc
      a.1 = tag (choose a) := (hchoose a).symm
      _ = tag (choose b) := congrArg tag hab'
      _ = b.1 := hchoose b
  refine ⟨P, htrueSource, prepay, hpreinj, ?_⟩
  intro d
  exact hlocalreal (choose d)

/-- This is the exact executable remaining-matching interface of the
full ORIGINAL eight-lane source ledger. A source-native local
prepayment exists *without assumptions*. If its literal UNPAID
full-source token subtype can be injectively matched to the literal
UNSPENT global credit subtype, the ORIGINAL full eight-debt numerical
payment follows. The residual injection is an EXPLICIT unproved
geometric resource hypothesis, not inferred from AngleCap. -/
theorem actual_eight_original_payment_of_remaining_matching
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ) (choice : V → Fin n) :
    ∃ P : Finset (actualEightSourceEarliestDebtTokens C exponent choice),
      (∀ d ∈ P, ∃ x : actualEarliestLossDebtTokenType C exponent choice,
        d = actual_eighth_token_as_full_source C exponent choice x) ∧
      ∃ prepay : {d : actualEightSourceEarliestDebtTokens C exponent choice //
          d ∈ P} → actualExternalPaymentCredits C exponent choice,
        Function.Injective prepay ∧
        ((∃ remaining :
          {d : actualEightSourceEarliestDebtTokens C exponent choice //
            d ∉ P} →
          {c : actualExternalPaymentCredits C exponent choice //
            c ∉ (Finset.univ : Finset
              {d : actualEightSourceEarliestDebtTokens C exponent choice //
                d ∈ P}).image prepay},
            Function.Injective remaining) →
          terminalTwinOtherFiveDebt C exponent +
            ((chosenLossActualEdgeBlockerTriples C exponent choice).biUnion
              (lossCoveredBlockerTripleWords C)).card +
            translatedLossDuplicateDebt C exponent choice ≤
          (lossLedgerOutsideTranslatedTrueHoles C exponent choice).card +
            terminalTwinAvailableSurplus C exponent) := by
  classical
  obtain ⟨P, htag, prepay, hinj, _hreal⟩ :=
    actual_eight_original_genuine_eighth_prepayment_exists
      C exponent choice
  refine ⟨P, htag, prepay, hinj, ?_⟩
  rintro ⟨remaining, hremaining⟩
  obtain ⟨whole, hwhole⟩ :=
    finite_prepaid_and_remaining_matching_glue P prepay hinj
      remaining hremaining
  exact actual_eight_source_earliest_debt_injection_implies_payment
    C exponent choice whole hwhole

#print axioms finite_prepaid_and_remaining_matching_glue
#print axioms actual_eighth_token_as_full_source_injective
#print axioms actual_eight_original_genuine_eighth_prepayment_exists
#print axioms actual_eight_original_payment_of_remaining_matching

end OrderedEdgeColoring
end JSP000404Research
