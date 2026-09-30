import JSP000404Research.ResidualFullExactOrderedDescendant
import JSP000404Research.ResidualExactPairStateClassification
import Mathlib.Tactic

/-!
# State classification of an exact one-flip full descendant

Two distinct exact full blockers are first normalized to an ordered residual
pair a<b.  The exact-pair classifier then leaves only three possibilities:

* active-safe: a deterministic residual transition is available;
* no-active-safe with both reduced exponents positive: the pair has the
  established local dyadic capacity bound;
* no-active-safe with at least one reduced-zero endpoint: this is the only
  recursive lossless state.

Free-tensor inheritance and nondecreasing overlap mass are retained in every
branch.
-/

namespace JSP000404Research
namespace OrderedEdgeColoring

theorem oneFlip_two_full_exact_descendant_state
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    {u v w z : V} {c : Fin n}
    {base : Fin n → Bool}
    (hbase :
      base ∈ retainedCompletionWords C u ∩
        retainedCompletionWords C v)
    (hcu : c ∈ retainedActive C u)
    (hcv : c ∈ retainedActive C v)
    (hw : w ∈ oneFlipFullBlockers C u v c)
    (hz : z ∈ oneFlipFullBlockers C u v c)
    (hwz : w ≠ z)
    (hwExact : ExactProjectedBudget C exponent w)
    (hzExact : ExactProjectedBudget C exponent z) :
    ∃ a b : V,
      a < b ∧
      IsResidual C a b ∧
      flipBoolWordAt base c ∈ retainedCompletionWords C a ∧
      flipBoolWordAt base c ∈ retainedCompletionWords C b ∧
      ExactProjectedBudget C exponent a ∧
      ExactProjectedBudget C exponent b ∧
      commonInactiveRetained C u v ⊆
        commonInactiveRetained C a b ∧
      (retainedCompletionWords C u ∩
        retainedCompletionWords C v).card ≤
        (retainedCompletionWords C a ∩
          retainedCompletionWords C b).card ∧
      (
        (
          ∃ e : Fin n,
            e ∉ residualForbidden C a b ∧
            ((e ∈ retainedActive C a ∧
                e ∉ retainedActive C b) ∨
             (e ∉ retainedActive C a ∧
                e ∈ retainedActive C b))
        )
        ∨
        (
          NoActiveSafeCoordinate C a b ∧
          (commonInactiveRetained C a b).card < exponent a ∧
          (commonInactiveRetained C a b).card < exponent b ∧
          2 ^ exponent a + 2 ^ exponent b
            ≤
          2 ^
            (n -
              ((incomingRetained C b).card +
               (outgoingRetained C a).card))
        )
        ∨
        (
          NoActiveSafeCoordinate C a b ∧
          (exponent a =
              (commonInactiveRetained C a b).card
           ∨
           exponent b =
              (commonInactiveRetained C a b).card)
        )
      ) := by
  obtain ⟨a,b,hab,hres,haWord,hbWord,
      haSat,hbSat,hfree,hmass⟩ :=
    oneFlip_two_full_exact_blockers_ordered_descendant
      C exponent hbase hcu hcv hw hz hwz hwExact hzExact
  refine ⟨a,b,hab,hres,haWord,hbWord,
    haSat,hbSat,hfree,hmass,?_⟩
  rcases
      exact_overlap_activeSafe_or_noActiveSafe_reduced_classification
        C exponent hab haWord hbWord haSat hbSat
    with hactive | hno
  · exact Or.inl hactive
  · obtain ⟨hNo,hred⟩ := hno
    rcases hred with hpos | haZero | hbZero
    · right
      left
      exact ⟨hNo,hpos.1,hpos.2,
        exact_overlap_noActiveSafe_positiveReduced_capacity
          C exponent hNo haWord hbWord haSat hbSat
          hpos.1 hpos.2⟩
    · exact Or.inr (Or.inr ⟨hNo,Or.inl haZero⟩)
    · exact Or.inr (Or.inr ⟨hNo,Or.inr hbZero⟩)

#print axioms oneFlip_two_full_exact_descendant_state

end OrderedEdgeColoring
end JSP000404Research
