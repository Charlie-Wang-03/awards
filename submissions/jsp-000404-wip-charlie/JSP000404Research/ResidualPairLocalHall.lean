
import JSP000404Research.ResidualSaturatedOverlapDecomposition
import JSP000404Research.ResidualLossWords
import Mathlib.Tactic

/-!
# Pair-local Hall balance for the final hard residual words

The remaining global hard-word problem is not caused by a local lack of
Boolean capacity.

For a saturated--saturated overlap carrier u,v we have

  card(Q_u) = 2^k(u),
  card(Q_v) = 2^k(v),

and in the lower branch every genuine centre exponent is strictly below n.
Hence

  2^k(u) + 2^k(v) <= 2^n.

Using

  card(Q_u union Q_v) + card(Q_u inter Q_v)
    = card(Q_u) + card(Q_v),

we obtain

  card(Q_u inter Q_v)
    <= 2^n - card(Q_u union Q_v).

Thus the overlap cube of one saturated--saturated carrier can always be
injected into Boolean words outside the union of its two endpoint cubes.

Likewise, an exact projected-loss vertex has exponent = projectedFree+1 <= n,
so its loss cube Q_v has size at most 2^(n-1); therefore it also admits a
pair-local copy inside the complement of Q_v.

The remaining difficulty is purely global: these local complement targets may
be occupied by other completion cubes, so they must be coordinated by an
augmenting/displacement argument.
-/

namespace JSP000404Research
namespace OrderedEdgeColoring

open scoped BigOperators

noncomputable def pairLocalHoles
    {V : Type*} [LinearOrder V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (u v : V) :
    Finset (Fin n → Bool) :=
  (Finset.univ : Finset (Fin n → Bool)) \
    (retainedCompletionWords C u ∪
      retainedCompletionWords C v)

noncomputable def vertexLocalHoles
    {V : Type*} [LinearOrder V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (v : V) :
    Finset (Fin n → Bool) :=
  (Finset.univ : Finset (Fin n → Bool)) \
    retainedCompletionWords C v

theorem two_pow_add_le_two_pow_of_both_lt
    {a b n : ℕ}
    (ha : a < n)
    (hb : b < n) :
    2 ^ a + 2 ^ b ≤ 2 ^ n := by
  have hn : 1 ≤ n := by omega
  have ha' : a ≤ n - 1 := by omega
  have hb' : b ≤ n - 1 := by omega
  have hpa :
      2 ^ a ≤ 2 ^ (n - 1) :=
    Nat.pow_le_pow_right (by norm_num : 0 < 2) ha'
  have hpb :
      2 ^ b ≤ 2 ^ (n - 1) :=
    Nat.pow_le_pow_right (by norm_num : 0 < 2) hb'
  have hpow :
      2 ^ n = 2 ^ (n - 1) + 2 ^ (n - 1) := by
    have hs : n - 1 + 1 = n := by omega
    calc
      2 ^ n = 2 ^ (n - 1 + 1) := by rw [hs]
      _ = 2 ^ (n - 1) * 2 := by rw [pow_succ]
      _ = 2 ^ (n - 1) + 2 ^ (n - 1) := by omega
  omega

theorem pairLocalHoles_card
    {V : Type*} [LinearOrder V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (u v : V) :
    (pairLocalHoles C u v).card =
      2 ^ n -
        (retainedCompletionWords C u ∪
          retainedCompletionWords C v).card := by
  classical
  unfold pairLocalHoles
  rw [Finset.card_sdiff_of_subset (Finset.subset_univ _)]
  simp [Fintype.card_fun]

theorem vertexLocalHoles_card
    {V : Type*} [LinearOrder V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (v : V) :
    (vertexLocalHoles C v).card =
      2 ^ n - (retainedCompletionWords C v).card := by
  classical
  unfold vertexLocalHoles
  rw [Finset.card_sdiff_of_subset (Finset.subset_univ _)]
  simp [Fintype.card_fun]

/-- One saturated--saturated carrier has enough complement capacity to pay its
entire overlap cube. -/
theorem saturated_pair_overlap_card_le_pairLocalHoles
    {V : Type*} [LinearOrder V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    {u v : V}
    (huSat : ExactProjectedBudget C exponent u)
    (hvSat : ExactProjectedBudget C exponent v)
    (huLt : exponent u < n)
    (hvLt : exponent v < n) :
    (retainedCompletionWords C u ∩
        retainedCompletionWords C v).card
      ≤
    (pairLocalHoles C u v).card := by
  have hsum :
      2 ^ exponent u + 2 ^ exponent v ≤ 2 ^ n :=
    two_pow_add_le_two_pow_of_both_lt huLt hvLt
  have hcardU :
      (retainedCompletionWords C u).card =
        2 ^ exponent u := by
    rw [retainedCompletionWords_card, huSat]
  have hcardV :
      (retainedCompletionWords C v).card =
        2 ^ exponent v := by
    rw [retainedCompletionWords_card, hvSat]
  have hunion :=
    Finset.card_union_add_card_inter
      (retainedCompletionWords C u)
      (retainedCompletionWords C v)
  rw [hcardU, hcardV] at hunion
  rw [pairLocalHoles_card]
  omega

/-- Cardinal Hall form: the saturated overlap cube injects into pair-local
holes. -/
theorem exists_saturated_pair_overlap_injection_to_local_holes
    {V : Type*} [LinearOrder V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    {u v : V}
    (huSat : ExactProjectedBudget C exponent u)
    (hvSat : ExactProjectedBudget C exponent v)
    (huLt : exponent u < n)
    (hvLt : exponent v < n) :
    ∃ f :
      {word : Fin n → Bool //
        word ∈ retainedCompletionWords C u ∩
          retainedCompletionWords C v} →
      {word : Fin n → Bool //
        word ∈ pairLocalHoles C u v},
      Function.Injective f := by
  classical
  exact Fintype.card_le_iff.mp
    (by
      simpa using
        saturated_pair_overlap_card_le_pairLocalHoles
          C exponent huSat hvSat huLt hvLt)

/-- Exact projected loss has a local complement at least as large as the loss
cube itself. -/
theorem projectedLoss_completion_card_le_vertexLocalHoles
    {V : Type*} [LinearOrder V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    {v : V}
    (hexp : exponent v ≤ n)
    (hloss :
      exponent v = projectedFree C v + 1) :
    (retainedCompletionWords C v).card ≤
      (vertexLocalHoles C v).card := by
  have hfreeLt :
      projectedFree C v < n := by
    rw [hloss] at hexp
    omega
  have hhalf :
      2 ^ projectedFree C v +
          2 ^ projectedFree C v ≤ 2 ^ n := by
    exact two_pow_add_le_two_pow_of_both_lt
      hfreeLt hfreeLt
  rw [vertexLocalHoles_card,
      retainedCompletionWords_card]
  omega

/-- Cardinal Hall form for one exact projected-loss cube. -/
theorem exists_projectedLoss_injection_to_local_holes
    {V : Type*} [LinearOrder V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    {v : V}
    (hexp : exponent v ≤ n)
    (hloss :
      exponent v = projectedFree C v + 1) :
    ∃ f :
      {word : Fin n → Bool //
        word ∈ retainedCompletionWords C v} →
      {word : Fin n → Bool //
        word ∈ vertexLocalHoles C v},
      Function.Injective f := by
  classical
  exact Fintype.card_le_iff.mp
    (by
      simpa using
        projectedLoss_completion_card_le_vertexLocalHoles
          C exponent hexp hloss)

#print axioms saturated_pair_overlap_card_le_pairLocalHoles
#print axioms exists_saturated_pair_overlap_injection_to_local_holes
#print axioms projectedLoss_completion_card_le_vertexLocalHoles
#print axioms exists_projectedLoss_injection_to_local_holes

end OrderedEdgeColoring
end JSP000404Research
