import JSP000404Research.ResidualNetCollisionCandidateShadowInjection
import Mathlib.Tactic

/-!
# AUDIT: rainbow matching capacity is IDENTICAL to ordinary matching capacity

A newly verified source-provenance-free fact changes the earlier
interpretation of the rainbow number: for a FIXED target diagonal d,
the shadow map sends every candidate exact-shell edge to a SOFT
completion word injectively. Flipping the same unordered pair of
colours at the same d necessarily produces the same shadow.

Therefore two DISTINCT candidate graph edges CANNOT reuse the same
unordered pair of flip colours. The earlier proposed strict refinement
"rainbow matching number <= ordinary matching number" is actually
EQUALITY for this PARTICULAR target-exact candidate graph.

This is an important nontrivial proof audit and correction to the
preceding research frontier, not a claimed improvement in the bound.
Rainbow source rigidity remains useful, but it does NOT eliminate
additional candidate matching configurations in this model.
-/

namespace JSP000404Research
namespace OrderedEdgeColoring

/-- Double Boolean coordinate flips depend only on the UNORDERED
two-element set when both pairs contain distinct coordinates. -/
theorem two_flip_same_word_of_same_unordered_colours
    {n : ℕ} (d : Fin n → Bool) (a b c f : Fin n)
    (hab : a ≠ b)
    (hpair : ({a, b} : Finset (Fin n)) = {c, f}) :
    flipCompletionWord a (flipCompletionWord b d) =
      flipCompletionWord c (flipCompletionWord f d) := by
  classical
  have ha : a = c ∨ a = f := by
    have hm : a ∈ ({c, f} : Finset (Fin n)) := by
      rw [← hpair]
      simp
    simpa only [Finset.mem_insert, Finset.mem_singleton] using hm
  have hb : b = c ∨ b = f := by
    have hm : b ∈ ({c, f} : Finset (Fin n)) := by
      rw [← hpair]
      simp
    simpa only [Finset.mem_insert, Finset.mem_singleton] using hm
  rcases ha with hac | haf
  · rcases hb with hbc | hbf
    · exact False.elim (hab (hac.trans hbc.symm))
    · subst c
      subst f
      rfl
  · rcases hb with hbc | hbf
    · subst f
      subst c
      exact flipCompletionWord_comm a b d hab
    · exact False.elim (hab (haf.trans hbf.symm))

/-- Every eligible target-specific candidate edge has TWO DISTINCT
original forward/reverse flip colours. This is true for the graph
itself, not only for its ACTUAL NET source edges. -/
theorem target_exact_shell_candidate_edge_colours_distinct
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ) (d : Fin n → Bool)
    (e : (V × Fin n) × (V × Fin n))
    (he : e ∈ targetExactShellSlotEdges C exponent d) :
    e.2.2 ≠ e.1.2 := by
  obtain ⟨_, _, _, hcf, hnotcr, _⟩ := Finset.mem_filter.mp he
  have hcfActive : e.2.2 ∈ retainedActive C e.1.1 :=
    (Finset.mem_filter.mp hcf).2.1
  intro h
  exact hnotcr (h ▸ hcfActive)

/-- FIXED TARGET candidate graph edges are ALREADY uniquely
determined by their unordered pair of two original flip colours.
The new shadow-word injection proves this without any hard-source
NET provenance assumption. -/
theorem target_exact_shell_colour_support_injective_on_edges
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ) (d : Fin n → Bool)
    (e f : (V × Fin n) × (V × Fin n))
    (he : e ∈ targetExactShellSlotEdges C exponent d)
    (hf : f ∈ targetExactShellSlotEdges C exponent d)
    (hcol : targetExactShellEdgeColourSupport e =
      targetExactShellEdgeColourSupport f) :
    e = f := by
  have hdistinct :=
    target_exact_shell_candidate_edge_colours_distinct C exponent d e he
  have hpair : ({e.2.2, e.1.2} : Finset (Fin n)) =
      {f.2.2, f.1.2} := by
    simpa only [targetExactShellEdgeColourSupport] using hcol
  have hshadow :=
    two_flip_same_word_of_same_unordered_colours d
      e.2.2 e.1.2 f.2.2 f.1.2 hdistinct hpair
  exact target_exact_shell_candidate_shadow_injective_on_edges
    C exponent d e f he hf hshadow

/-- In this candidate graph EVERY finite ordinary slot matching
is AUTOMATICALLY a rainbow matching. The colour-support restriction
is already a consequence of edge eligibility and soft-shadow
uniqueness, not an additional graph-cutting restriction. -/
theorem target_exact_shell_ordinary_matching_is_rainbow
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ) (d : Fin n → Bool)
    (M : Finset ((V × Fin n) × (V × Fin n)))
    (hsub : M ⊆ targetExactShellSlotEdges C exponent d)
    (hl : ∀ e ∈ M, ∀ f ∈ M, e.1 = f.1 → e = f)
    (hr : ∀ e ∈ M, ∀ f ∈ M, e.2 = f.2 → e = f) :
    targetExactShellRainbowMatching C exponent d M := by
  refine ⟨hsub, hl, hr, ?_⟩
  intro e he f hf hcol
  exact target_exact_shell_colour_support_injective_on_edges
    C exponent d e f (hsub he) (hsub hf) hcol

/-- For these genuine-source-compatible exact-shell candidate
graphs, the purported rainbow matching improvement is vacuous:
the TWO FINITE matching numbers are ALWAYS EQUAL. -/
theorem target_exact_shell_rainbow_matching_number_eq_ordinary
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ) (d : Fin n → Bool) :
    targetExactShellRainbowMatchingNumber C exponent d =
      targetExactShellSlotMatchingNumber C exponent d := by
  apply Nat.le_antisymm
  · exact exact_shell_rainbow_matching_number_le_ordinary_matching_number
      C exponent d
  · classical
    unfold targetExactShellSlotMatchingNumber
    apply Finset.sup_le
    intro M hM
    have hdata :
        M ⊆ targetExactShellSlotEdges C exponent d ∧
        (∀ e ∈ M, ∀ f ∈ M, e.1 = f.1 → e = f) ∧
        (∀ e ∈ M, ∀ f ∈ M, e.2 = f.2 → e = f) :=
      (Finset.mem_filter.mp hM).2
    exact exact_shell_rainbow_matching_card_le_rainbow_number
      C exponent d M
      (target_exact_shell_ordinary_matching_is_rainbow
        C exponent d M hdata.1 hdata.2.1 hdata.2.2)

/-- Even the RAW candidate edge graph has no repeated unordered
transport flip pair, so every pair of distinct candidate edges
necessarily differs in its unordered colour support. -/
theorem target_exact_shell_distinct_edges_distinct_colour_support
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ) (d : Fin n → Bool)
    (e f : (V × Fin n) × (V × Fin n))
    (he : e ∈ targetExactShellSlotEdges C exponent d)
    (hf : f ∈ targetExactShellSlotEdges C exponent d)
    (hne : e ≠ f) :
    targetExactShellEdgeColourSupport e ≠
      targetExactShellEdgeColourSupport f := by
  intro hcol
  exact hne (target_exact_shell_colour_support_injective_on_edges
    C exponent d e f he hf hcol)

#print axioms two_flip_same_word_of_same_unordered_colours
#print axioms target_exact_shell_candidate_edge_colours_distinct
#print axioms target_exact_shell_colour_support_injective_on_edges
#print axioms target_exact_shell_ordinary_matching_is_rainbow
#print axioms target_exact_shell_rainbow_matching_number_eq_ordinary
#print axioms target_exact_shell_distinct_edges_distinct_colour_support

end OrderedEdgeColoring
end JSP000404Research
