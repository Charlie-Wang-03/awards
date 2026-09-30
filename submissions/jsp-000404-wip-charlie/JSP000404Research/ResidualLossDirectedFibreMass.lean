import JSP000404Research.ResidualLossDirectedFibre
import JSP000404Research.ResidualLossFibreRank
import JSP000404Research.OrderedPrefixGeometricSum
import JSP000404Research.OrderedSuffixGeometricSum
import JSP000404Research.ResidualCompletionIntersection
import Mathlib.Tactic

/-!
# Geometric completion-mass bounds for directed loss fibres

Under an outgoing loss-coordinate choice every translated-loss fibre is
all-true. Prefix ranks inject into retainedActive, yielding the exact finite
geometric-series bound on carrier completion mass.

Under an incoming choice every fibre is all-false. Suffix ranks give the
symmetric bound directly.
-/

namespace JSP000404Research
namespace OrderedEdgeColoring

theorem outgoing_translatedLossFibre_completion_mass_bound
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexp : ∀ v, exponent v ≤ n)
    (honeLoss :
      ∀ v, (active C v).card ≤ n - exponent v + 1)
    (choice : V → Fin n)
    (hchoice :
      ∀ v,
        v ∈ projectedLossVertices C exponent →
        choice v ∈ outgoingRetained C v)
    (word : Fin n → Bool) :
    (∑ v ∈ translatedLossFibre C exponent choice word,
        (retainedCompletionWords C v).card)
      ≤
    2 ^ n -
      2 ^ (n -
        (translatedLossFibre C exponent choice word).card) := by
  classical
  let F := translatedLossFibre C exponent choice word
  have hactive :
      ∀ v, v ∈ F → choice v ∈ retainedActive C v := by
    intro v hv
    have hvData :=
      (mem_translatedLossFibre
        C exponent choice word v).1 hv
    exact outgoingRetained_subset_retainedActive C v
      (hchoice v hvData.1)
  have hallTrue :
      ∀ v, v ∈ F → word (choice v) = true :=
    outgoing_choice_translatedLossFibre_all_true
      C exponent choice hchoice word
  have haN :
      ∀ v ∈ F, (retainedActive C v).card ≤ n := by
    intro v hv
    simpa using Finset.card_le_univ (retainedActive C v)
  have hrank :
      ∀ v ∈ F,
        (F.filter fun u => u ≤ v).card ≤
          (retainedActive C v).card := by
    intro v hv
    have hpref :=
      true_top_prefix_card_le_retainedActive
        C exponent hexp honeLoss choice word hactive
        hv (hallTrue v hv)
    simpa [F, translatedLossFibrePrefix] using hpref
  have hgeom :=
    ordered_prefix_geometric_sum_bound
      F (fun v => (retainedActive C v).card) n
      haN hrank
  calc
    (∑ v ∈ F, (retainedCompletionWords C v).card)
        =
      ∑ v ∈ F, 2 ^ (n - (retainedActive C v).card) := by
        apply Finset.sum_congr rfl
        intro v hv
        exact retainedCompletionWords_card C v
    _ ≤ 2 ^ n - 2 ^ (n - F.card) := hgeom

theorem incoming_translatedLossFibre_completion_mass_bound
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexp : ∀ v, exponent v ≤ n)
    (honeLoss :
      ∀ v, (active C v).card ≤ n - exponent v + 1)
    (choice : V → Fin n)
    (hchoice :
      ∀ v,
        v ∈ projectedLossVertices C exponent →
        choice v ∈ incomingRetained C v)
    (word : Fin n → Bool) :
    (∑ v ∈ translatedLossFibre C exponent choice word,
        (retainedCompletionWords C v).card)
      ≤
    2 ^ n -
      2 ^ (n -
        (translatedLossFibre C exponent choice word).card) := by
  classical
  let F := translatedLossFibre C exponent choice word
  have hactive :
      ∀ v, v ∈ F → choice v ∈ retainedActive C v := by
    intro v hv
    have hvData :=
      (mem_translatedLossFibre
        C exponent choice word v).1 hv
    exact incomingRetained_subset_retainedActive C v
      (hchoice v hvData.1)
  have hallFalse :
      ∀ v, v ∈ F → word (choice v) = false :=
    incoming_choice_translatedLossFibre_all_false
      C exponent choice hchoice word
  have haN :
      ∀ v ∈ F, (retainedActive C v).card ≤ n := by
    intro v hv
    simpa using Finset.card_le_univ (retainedActive C v)
  have hrank :
      ∀ v ∈ F,
        (F.filter fun w => v ≤ w).card ≤
          (retainedActive C v).card := by
    intro v hv
    have hsuf :=
      false_bottom_suffix_card_le_retainedActive
        C exponent hexp honeLoss choice word hactive
        hv (hallFalse v hv)
    simpa [F, translatedLossFibreSuffix] using hsuf
  have hgeom :=
    ordered_suffix_geometric_sum_bound
      F (fun v => (retainedActive C v).card) n
      haN hrank
  calc
    (∑ v ∈ F, (retainedCompletionWords C v).card)
        =
      ∑ v ∈ F, 2 ^ (n - (retainedActive C v).card) := by
        apply Finset.sum_congr rfl
        intro v hv
        exact retainedCompletionWords_card C v
    _ ≤ 2 ^ n - 2 ^ (n - F.card) := hgeom

#print axioms outgoing_translatedLossFibre_completion_mass_bound
#print axioms incoming_translatedLossFibre_completion_mass_bound

end OrderedEdgeColoring
end JSP000404Research
