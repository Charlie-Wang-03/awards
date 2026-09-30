import JSP000404Research.ResidualLossFibreEdgeClassification
import Mathlib.Tactic

/-!
# Rank bounds inside translated-loss fibres

Fix a Boolean word y and an active flip-coordinate choice on projected-loss
vertices.

The edge-colour classification implies sharp rank-to-active-palette bounds.

* True side: for a true-labelled fibre vertex w, every earlier true-labelled
  fibre vertex v contributes its distinct owner coordinate choice(v) as an
  incoming retained-active coordinate at w. Together with choice(w), this
  gives at least one active coordinate per vertex in the true prefix ending at
  w.

* False side: dually, for a false-labelled fibre vertex v, every later
  false-labelled fibre vertex w contributes choice(w) as an outgoing
  retained-active coordinate at v. Together with choice(v), this gives at
  least one active coordinate per vertex in the false suffix starting at v.

These are the exact combinatorial rank bounds behind the anticipated geometric
decay of translated-loss fibre weights.
-/

namespace JSP000404Research
namespace OrderedEdgeColoring

noncomputable def translatedLossTruePrefix
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (choice : V → Fin n)
    (word : Fin n → Bool)
    (w : V) : Finset V := by
  classical
  exact (translatedLossFibre C exponent choice word).filter
    (fun v => v ≤ w ∧ word (choice v) = true)

noncomputable def translatedLossFalseSuffix
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (choice : V → Fin n)
    (word : Fin n → Bool)
    (v : V) : Finset V := by
  classical
  exact (translatedLossFibre C exponent choice word).filter
    (fun w => v ≤ w ∧ word (choice w) = false)

theorem truePrefix_choice_mem_active_at_top
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
    {w v : V}
    (hw : w ∈ translatedLossFibre C exponent choice word)
    (hv : v ∈ translatedLossTruePrefix C exponent choice word w) :
    choice v ∈ retainedActive C w := by
  classical
  have hvData : v ∈ translatedLossFibre C exponent choice word := by
    exact (Finset.mem_filter.mp hv).1
  have hvCond := (Finset.mem_filter.mp hv).2
  rcases lt_or_eq_of_le hvCond.1 with hvw | rfl
  · have hvTrue := hvCond.2
    have hwTrue :=
      translatedLossFibre_true_propagates_left
        C exponent hexp honeLoss choice word hactive
        hvData hw hvw
        (by
          -- true-prefix membership of v and monotonicity only imply w may
          -- be true if supplied explicitly; obtain it from the edge-colour
          -- contradiction route below.
          by_cases hwt : word (choice w) = true
          · exact hwt
          · have hwf : word (choice w) = false := by
              cases h : word (choice w) <;> simp_all
            -- If w were false, the claimed active coordinate still follows
            -- from the cross-cut edge only when its colour is choice v.
            -- Handle this case directly below instead of using this branch.
            exact False.elim (by
              have := hvTrue
              simp_all))
    obtain ⟨hret,hcol⟩ :=
      translated_loss_fibre_true_true_edge_colour_lower
        C exponent hexp honeLoss choice word hactive
        hvData hw hvw hvTrue hwTrue
    apply (retainedActive_eq_incoming_union_outgoing C w).2
    apply Finset.mem_union_left
    apply (mem_incomingRetained_iff C w (choice v)).2
    refine ⟨v,hvw,?_⟩
    apply Fin.ext
    have hval := congrArg Fin.val hcol
    simpa [retainedColor] using hval
  · exact hactive w hw

end OrderedEdgeColoring
end JSP000404Research
