import JSP000404Research.ResidualLossDirectedFibre
import JSP000404Research.ResidualLossFibreRank
import JSP000404Research.OrderedPrefixGeometricSum
import JSP000404Research.ResidualCompletionIntersection
import Mathlib.Tactic

/-!
# Geometric completion-mass bounds for directed loss fibres

Under an outgoing loss-coordinate choice every translated-loss fibre is
all-true.  Hence for each fibre vertex v, its whole fibre prefix injects into
retainedActive(v).  Applying the abstract ordered-prefix geometric sum bound to

  a(v) = card(retainedActive(v))

gives a sharp bound on the total original completion mass of all carriers in
one translated word fibre.

The incoming case is the order-dual statement, obtained by applying the same
prefix lemma to the reversed order.
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
    _ ≤
      2 ^ n - 2 ^ (n - F.card) := hgeom

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

  -- Reverse the ambient order so suffix ranks become prefix ranks.
  letI revOrder : LinearOrder (OrderDual V) := inferInstance
  let Fd : Finset (OrderDual V) := F.map OrderDual.toDualEmbedding
  let ad : OrderDual V → ℕ :=
    fun v => (retainedActive C (OrderDual.ofDual v)).card

  have haN :
      ∀ v ∈ Fd, ad v ≤ n := by
    intro v hv
    simpa [ad] using
      Finset.card_le_univ (retainedActive C (OrderDual.ofDual v))

  have hrank :
      ∀ vd ∈ Fd,
        (Fd.filter fun ud => ud ≤ vd).card ≤ ad vd := by
    intro vd hvd
    obtain ⟨v,hvF,rfl⟩ := Finset.mem_map.mp hvd
    have hsuf :=
      false_bottom_suffix_card_le_retainedActive
        C exponent hexp honeLoss choice word hactive
        hvF (hallFalse v hvF)
    have hcardEq :
        (Fd.filter fun ud => ud ≤ OrderDual.toDual v).card =
          (translatedLossFibreSuffix C exponent choice word v).card := by
      classical
      apply Finset.card_bij
        (fun ud hud => OrderDual.ofDual ud)
      · intro ud hud
        have hudData := Finset.mem_filter.mp hud
        obtain ⟨u,huF,huEq⟩ := Finset.mem_map.mp hudData.1
        subst ud
        apply (mem_translatedLossFibreSuffix
          C exponent choice word v u).2
        exact ⟨huF, hudData.2⟩
      · intro ud hud
        rfl
      · intro ud₁ h₁ ud₂ h₂ hEq
        exact OrderDual.toDual_injective hEq
      · intro u hu
        have huData :=
          (mem_translatedLossFibreSuffix
            C exponent choice word v u).1 hu
        refine ⟨OrderDual.toDual u, ?_, rfl⟩
        apply Finset.mem_filter.mpr
        constructor
        · exact Finset.mem_map.mpr ⟨u,huData.1,rfl⟩
        · exact huData.2
    simpa [ad, hcardEq] using hsuf

  have hgeom :=
    ordered_prefix_geometric_sum_bound
      Fd ad n haN hrank
  have hsumEq :
      (∑ v ∈ F, 2 ^ (n - (retainedActive C v).card)) =
        ∑ vd ∈ Fd, 2 ^ (n - ad vd) := by
    classical
    rw [Finset.sum_map]
    simp [Fd, ad]
  have hcardFd : Fd.card = F.card := by
    simp [Fd]
  calc
    (∑ v ∈ F, (retainedCompletionWords C v).card)
        =
      ∑ v ∈ F, 2 ^ (n - (retainedActive C v).card) := by
        apply Finset.sum_congr rfl
        intro v hv
        exact retainedCompletionWords_card C v
    _ = ∑ vd ∈ Fd, 2 ^ (n - ad vd) := hsumEq
    _ ≤ 2 ^ n - 2 ^ (n - Fd.card) := hgeom
    _ = 2 ^ n - 2 ^ (n - F.card) := by rw [hcardFd]

#print axioms outgoing_translatedLossFibre_completion_mass_bound
#print axioms incoming_translatedLossFibre_completion_mass_bound

end OrderedEdgeColoring
end JSP000404Research
