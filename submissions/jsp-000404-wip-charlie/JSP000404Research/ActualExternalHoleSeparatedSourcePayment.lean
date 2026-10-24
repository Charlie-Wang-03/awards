import JSP000404Research.ActualExternalHoleNonreuseCertificate
import Mathlib.Tactic

/-!
# Three independently constructed debt maps with proven NONOVERLAP

Separately mapping genuine twin/other-five, actual blocker words and
translated-loss duplicate debt is not sufficient for global payment:
their images must be disjoint ACROSS categories. This lemma makes all
three forbidden cross-payments explicit, then composes the maps into
ONE globally injective, source-tagged allocation.

The result is conditional on REAL maps and REAL cross-disjointness;
it neither fabricates holes nor asserts such maps always exist
under planar AngleCap geometry.
-/
namespace JSP000404Research
namespace OrderedEdgeColoring

/-- Three source maps form a joint injection only when each is injective
and all three cross-image overlaps are excluded. -/
theorem three_source_maps_joint_injective
    {A B C R : Type*}
    (f : A → R) (g : B → R) (h : C → R)
    (hf : Function.Injective f)
    (hg : Function.Injective g)
    (hh : Function.Injective h)
    (hfg : ∀ a b, f a ≠ g b)
    (hfh : ∀ a c, f a ≠ h c)
    (hgh : ∀ b c, g b ≠ h c) :
    Function.Injective (Sum.elim f (Sum.elim g h)) := by
  intro x y heq
  cases x with
  | inl a =>
    cases y with
    | inl b =>
      exact congrArg Sum.inl (hf heq)
    | inr y =>
      cases y with
      | inl b => exact False.elim (hfg a b heq)
      | inr c => exact False.elim (hfh a c heq)
  | inr x =>
    cases x with
    | inl a =>
      cases y with
      | inl b => exact False.elim (hfg b a heq.symm)
      | inr y =>
        cases y with
        | inl b =>
          exact congrArg Sum.inr (congrArg Sum.inl (hg heq))
        | inr c => exact False.elim (hgh a c heq)
    | inr a =>
      cases y with
      | inl b => exact False.elim (hfh b a heq.symm)
      | inr y =>
        cases y with
        | inl b => exact False.elim (hgh b a heq.symm)
        | inr c =>
          exact congrArg Sum.inr (congrArg Sum.inr (hh heq))

/-- A sufficient, checkable actual payment condition:
  * three source maps land in the actual external-hole/unreserved-surplus
    type, not in covered shadows;
  * they are individually injections;
  * no target token is reused between any two debt classes.

This uses actual covered-blocker words as subtype debt witnesses;
no debt amount is silently dropped. -/
theorem three_separated_actual_debt_payments_suffice
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (B : OrderedEdgeColoring V (n + 1))
    (k : V → ℕ) (choice : V → Fin n)
    (f :
      Fin (terminalTwinOtherFiveDebt B k) →
        actualExternalPaymentCredits B k choice)
    (g :
      {w : Fin n → Bool //
        w ∈ (chosenLossActualEdgeBlockerTriples B k choice).biUnion
          (lossCoveredBlockerTripleWords B)} →
        actualExternalPaymentCredits B k choice)
    (h :
      Fin (translatedLossDuplicateDebt B k choice) →
        actualExternalPaymentCredits B k choice)
    (hf : Function.Injective f)
    (hg : Function.Injective g)
    (hh : Function.Injective h)
    (hfg : ∀ a b, f a ≠ g b)
    (hfh : ∀ a c, f a ≠ h c)
    (hgh : ∀ b c, g b ≠ h c) :
    terminalTwinOtherFiveDebt B k +
        ((chosenLossActualEdgeBlockerTriples B k choice).biUnion
          (lossCoveredBlockerTripleWords B)).card +
        translatedLossDuplicateDebt B k choice ≤
      (lossLedgerOutsideTranslatedTrueHoles B k choice).card +
        terminalTwinAvailableSurplus B k := by
  apply actual_external_hole_nonreuse_certificate_implies_payment
    B k choice (Sum.elim f (Sum.elim g h))
  exact three_source_maps_joint_injective
    f g h hf hg hh hfg hfh hgh

#print axioms three_source_maps_joint_injective
#print axioms three_separated_actual_debt_payments_suffice
end OrderedEdgeColoring
end JSP000404Research
