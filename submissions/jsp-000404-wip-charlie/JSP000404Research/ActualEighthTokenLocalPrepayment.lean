import JSP000404Research.ActualEighthOriginalLocalSection
import JSP000404Research.ResidualLossCanonicalRecordDebtEquiv
import Mathlib.Tactic

/-!
# Universal honest eighth-DEBT-TOKEN local prepayment

The canonical eighth source lane in actualEightSourceEarliestDebtTokens
is the DEPENDENT earliest-prior-loss debt token type, not the ambient
triple type. The earlier proved genuine equivalence converts each
dependent token to one actual earliest-prior collision record.

The universal record-level real-hole section can be pulled back along
this equivalence, giving a genuinely source-typed and injective
payment of ONE original eighth-debt token to each actual locally
eligible exterior hole. It consumes only the REAL TRUE-HOLE part of
the two original legal global credit types.

This is a partial EIGHTH LANE payment, not an allocation of the
remaining source tokens or the other seven classes. No full AngleCap
global payment is asserted.
-/

namespace JSP000404Research
namespace OrderedEdgeColoring

/-- Select genuine dependent eighth-debt tokens via their ACTUAL
earliest-prior record under the independently proved equivalence,
and match them injectively to original outside-translated TRUE-hole
global credits. The selection and injection work at arbitrary Boolean
width and any genuine projected-loss-centre cardinality. -/
theorem actual_eighth_allwidth_dependent_tokens_local_credit_injection
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ) (choice : V → Fin n) :
    ∃ T : Finset (Fin n × Fin n × (Fin n → Bool)),
      T ⊆ actualEarliestLossCollisionRecords C exponent choice ∧
      T.image (fun a : Fin n × Fin n × (Fin n → Bool) =>
        flipBoolWordAt (flipBoolWordAt a.2.2 a.1) a.2.1) =
          actualLossEarliestEligibleLocalHoles C exponent choice ∧
      ∃ allocation :
          {x : actualEarliestLossDebtTokenType C exponent choice //
            (actualEarliestLossDebtEquivCollisionRecord
              C exponent choice x).1 ∈ T} →
            actualExternalPaymentCredits C exponent choice,
        Function.Injective allocation ∧
        ∀ x, ∃ q : {q : Fin n → Bool //
            q ∈ lossLedgerOutsideTranslatedTrueHoles C exponent choice},
          allocation x = Sum.inl q := by
  classical
  obtain ⟨T, hsubset, himage, alloc, hinj, hall⟩ :=
    actual_eighth_allwidth_local_section_injects_into_global_credits
      C exponent choice
  let e := actualEarliestLossDebtEquivCollisionRecord C exponent choice
  let asRecord :
      {x : actualEarliestLossDebtTokenType C exponent choice //
        (e x).1 ∈ T} →
      {a : Fin n × Fin n × (Fin n → Bool) // a ∈ T} :=
    fun x => ⟨(e x.1).1, x.2⟩
  have hrecinj : Function.Injective asRecord := by
    intro x y hxy
    have hval : (e x.1).1 = (e y.1).1 :=
      congrArg Subtype.val hxy
    have heq : e x.1 = e y.1 := Subtype.ext hval
    exact Subtype.ext (e.injective heq)
  let payment :
      {x : actualEarliestLossDebtTokenType C exponent choice //
        (e x).1 ∈ T} →
      actualExternalPaymentCredits C exponent choice :=
    fun x => alloc (asRecord x)
  have hpayinj : Function.Injective payment := by
    intro x y hxy
    exact hrecinj (hinj hxy)
  refine ⟨T, hsubset, himage, payment, hpayinj, ?_⟩
  intro x
  obtain ⟨q, hq, _⟩ := hall (asRecord x)
  exact ⟨q, hq⟩

#print axioms actual_eighth_allwidth_dependent_tokens_local_credit_injection

end OrderedEdgeColoring
end JSP000404Research
