import JSP000404Research.ResidualLossFibreEdgeClassification
import Mathlib.Tactic

/-!
# Rank bounds inside translated-loss fibres

Fix a Boolean word y and an active flip-coordinate choice on projected-loss
vertices.

If a fibre vertex w is true-labelled, monotonicity forces every earlier fibre
vertex to be true-labelled as well. The true--true edge classification then
says that each earlier vertex v contributes its distinct owner coordinate
choice(v) as an incoming retained-active coordinate at w. Together with
choice(w), this injects the whole fibre prefix up to w into retainedActive(w).

Dually, if v is false-labelled, every later fibre vertex is false-labelled,
and each later owner coordinate is outgoing retained-active at v. Hence the
fibre suffix from v injects into retainedActive(v).

These are the exact rank-to-active-palette inequalities behind geometric
decay on the two monotone sides of one translated-loss fibre.
-/

namespace JSP000404Research
namespace OrderedEdgeColoring

noncomputable def translatedLossFibrePrefix
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (choice : V → Fin n)
    (word : Fin n → Bool)
    (w : V) : Finset V := by
  classical
  exact (translatedLossFibre C exponent choice word).filter
    (fun v => v ≤ w)

noncomputable def translatedLossFibreSuffix
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (choice : V → Fin n)
    (word : Fin n → Bool)
    (v : V) : Finset V := by
  classical
  exact (translatedLossFibre C exponent choice word).filter
    (fun w => v ≤ w)

@[simp] theorem mem_translatedLossFibrePrefix
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (choice : V → Fin n)
    (word : Fin n → Bool)
    (w v : V) :
    v ∈ translatedLossFibrePrefix C exponent choice word w ↔
      v ∈ translatedLossFibre C exponent choice word ∧ v ≤ w := by
  classical
  simp [translatedLossFibrePrefix]

@[simp] theorem mem_translatedLossFibreSuffix
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (choice : V → Fin n)
    (word : Fin n → Bool)
    (v w : V) :
    w ∈ translatedLossFibreSuffix C exponent choice word v ↔
      w ∈ translatedLossFibre C exponent choice word ∧ v ≤ w := by
  classical
  simp [translatedLossFibreSuffix]

theorem true_top_prefix_choice_mapsTo_active
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexp : ∀ v, exponent v ≤ n)
    (honeLoss :
      ∀ v, (active C v).card ≤ n - exponent v + 1)
    (choice : V → Fin n)
    (word : Fin n → Bool)
    (hactive :
      ∀ x,
        x ∈ translatedLossFibre C exponent choice word →
        choice x ∈ retainedActive C x)
    {w : V}
    (hw : w ∈ translatedLossFibre C exponent choice word)
    (hwTrue : word (choice w) = true) :
    Set.MapsTo choice
      (translatedLossFibrePrefix C exponent choice word w : Set V)
      (retainedActive C w : Set (Fin n)) := by
  intro v hv
  have hvData :=
    (mem_translatedLossFibrePrefix
      C exponent choice word w v).1 hv
  rcases lt_or_eq_of_le hvData.2 with hvw | rfl
  · have hvTrue :=
      translatedLossFibre_true_propagates_left
        C exponent hexp honeLoss choice word hactive
        hvData.1 hw hvw hwTrue
    obtain ⟨hret,hcol⟩ :=
      translated_loss_fibre_true_true_edge_colour_lower
        C exponent hexp honeLoss choice word hactive
        hvData.1 hw hvw hvTrue hwTrue
    rw [retainedActive_eq_incoming_union_outgoing C w]
    apply Finset.mem_union_left
    apply (mem_incomingRetained_iff C w (choice v)).2
    refine ⟨v,hvw,?_⟩
    apply Fin.ext
    have hval := congrArg Fin.val hcol
    simpa [retainedColor] using hval
  · exact hactive w hw

theorem false_bottom_suffix_choice_mapsTo_active
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexp : ∀ v, exponent v ≤ n)
    (honeLoss :
      ∀ v, (active C v).card ≤ n - exponent v + 1)
    (choice : V → Fin n)
    (word : Fin n → Bool)
    (hactive :
      ∀ x,
        x ∈ translatedLossFibre C exponent choice word →
        choice x ∈ retainedActive C x)
    {v : V}
    (hv : v ∈ translatedLossFibre C exponent choice word)
    (hvFalse : word (choice v) = false) :
    Set.MapsTo choice
      (translatedLossFibreSuffix C exponent choice word v : Set V)
      (retainedActive C v : Set (Fin n)) := by
  intro w hw
  have hwData :=
    (mem_translatedLossFibreSuffix
      C exponent choice word v w).1 hw
  rcases lt_or_eq_of_le hwData.2 with hvw | hvwEq
  · have hwFalse :=
      translatedLossFibre_false_propagates_right
        C exponent hexp honeLoss choice word hactive
        hv hwData.1 hvw hvFalse
    obtain ⟨hret,hcol⟩ :=
      translated_loss_fibre_false_false_edge_colour_upper
        C exponent hexp honeLoss choice word hactive
        hv hwData.1 hvw hvFalse hwFalse
    rw [retainedActive_eq_incoming_union_outgoing C v]
    apply Finset.mem_union_right
    apply (mem_outgoingRetained_iff C v (choice w)).2
    refine ⟨w,hvw,?_⟩
    apply Fin.ext
    have hval := congrArg Fin.val hcol
    simpa [retainedColor] using hval
  · subst w
    exact hactive v hv

theorem true_top_prefix_card_le_retainedActive
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexp : ∀ v, exponent v ≤ n)
    (honeLoss :
      ∀ v, (active C v).card ≤ n - exponent v + 1)
    (choice : V → Fin n)
    (word : Fin n → Bool)
    (hactive :
      ∀ x,
        x ∈ translatedLossFibre C exponent choice word →
        choice x ∈ retainedActive C x)
    {w : V}
    (hw : w ∈ translatedLossFibre C exponent choice word)
    (hwTrue : word (choice w) = true) :
    (translatedLossFibrePrefix C exponent choice word w).card ≤
      (retainedActive C w).card := by
  classical
  exact Finset.card_le_card_of_injOn
    choice
    (true_top_prefix_choice_mapsTo_active
      C exponent hexp honeLoss choice word hactive hw hwTrue)
    ((translatedLossFibre_choice_injective
      C exponent hexp honeLoss choice word).mono
      (by
        intro x hx
        exact (mem_translatedLossFibrePrefix
          C exponent choice word w x).1 hx |>.1))

theorem false_bottom_suffix_card_le_retainedActive
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexp : ∀ v, exponent v ≤ n)
    (honeLoss :
      ∀ v, (active C v).card ≤ n - exponent v + 1)
    (choice : V → Fin n)
    (word : Fin n → Bool)
    (hactive :
      ∀ x,
        x ∈ translatedLossFibre C exponent choice word →
        choice x ∈ retainedActive C x)
    {v : V}
    (hv : v ∈ translatedLossFibre C exponent choice word)
    (hvFalse : word (choice v) = false) :
    (translatedLossFibreSuffix C exponent choice word v).card ≤
      (retainedActive C v).card := by
  classical
  exact Finset.card_le_card_of_injOn
    choice
    (false_bottom_suffix_choice_mapsTo_active
      C exponent hexp honeLoss choice word hactive hv hvFalse)
    ((translatedLossFibre_choice_injective
      C exponent hexp honeLoss choice word).mono
      (by
        intro x hx
        exact (mem_translatedLossFibreSuffix
          C exponent choice word v x).1 hx |>.1))

#print axioms true_top_prefix_card_le_retainedActive
#print axioms false_bottom_suffix_card_le_retainedActive

end OrderedEdgeColoring
end JSP000404Research
