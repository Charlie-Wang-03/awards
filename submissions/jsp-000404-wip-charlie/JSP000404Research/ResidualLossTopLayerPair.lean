import JSP000404Research.ResidualLossStarCrossBound
import JSP000404Research.ResidualLossStarCapacity
import Mathlib.Tactic

/-!
# Two top-layer projected-loss stars tile the Boolean cube

Suppose u,v are distinct projected-loss vertices with

  exponent(u)=exponent(v)=n-1.

Each has projected free dimension n-2 and exactly two retained-active
coordinates.  Hence each rich active-star block has size

  3 * 2^(n-2).

The general loss-star cross bound gives

  card(Star(u) ∩ Star(v))
    <= card(Q_u)+card(Q_v)
    = 2 * 2^(n-2).

On the other hand both stars lie in the ambient Boolean n-cube of size 2^n,
so inclusion--exclusion forces the reverse inequality.  Consequently equality
holds throughout:

  card intersection = 2^(n-1),
  card union = 2^n.

Thus the two top-layer loss stars form an exact Hall-tight cover of the entire
Boolean cube.
-/

namespace JSP000404Research
namespace OrderedEdgeColoring

theorem projectedLoss_topLayer_completion_card
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    {v : V}
    (hvLoss : v ∈ projectedLossVertices C exponent)
    (hvTop : exponent v = n - 1) :
    (retainedCompletionWords C v).card = 2 ^ (n - 2) := by
  rw [retainedCompletionWords_card]
  have hloss :=
    (mem_projectedLossVertices C exponent v).1 hvLoss
  unfold projectedFree at hloss
  have hact :
      (retainedActive C v).card ≤ n := by
    simpa using Finset.card_le_univ (retainedActive C v)
  have hfree :
      n - (retainedActive C v).card = n - 2 := by
    omega
  rw [hfree]

theorem projectedLoss_topLayer_activeStar_card
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    {v : V}
    (hvLoss : v ∈ projectedLossVertices C exponent)
    (hvTop : exponent v = n - 1) :
    (activeStarCandidateBlock C v).card =
      3 * 2 ^ (n - 2) := by
  rw [activeStarCandidateBlock_card,
      projectedLoss_retainedActive_card C exponent hvLoss,
      projectedLoss_topLayer_completion_card
        C exponent hvLoss hvTop]
  have hn2 : 2 ≤ n := by
    have hloss :=
      (mem_projectedLossVertices C exponent v).1 hvLoss
    unfold projectedFree at hloss
    have hfreeNonneg : 0 ≤ projectedFree C v := Nat.zero_le _
    omega
  omega

theorem two_topLayer_lossStars_intersection_card
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexp : ∀ x, exponent x ≤ n)
    (honeLoss :
      ∀ x, (active C x).card ≤ n - exponent x + 1)
    {u v : V}
    (huLoss : u ∈ projectedLossVertices C exponent)
    (hvLoss : v ∈ projectedLossVertices C exponent)
    (huv : u ≠ v)
    (huTop : exponent u = n - 1)
    (hvTop : exponent v = n - 1) :
    (activeStarCandidateBlock C u ∩
      activeStarCandidateBlock C v).card =
      2 ^ (n - 1) := by
  have hn2 : 2 ≤ n := by
    have huEq :=
      (mem_projectedLossVertices C exponent u).1 huLoss
    unfold projectedFree at huEq
    omega
  have hqU :=
    projectedLoss_topLayer_completion_card
      C exponent huLoss huTop
  have hqV :=
    projectedLoss_topLayer_completion_card
      C exponent hvLoss hvTop
  have hstarU :=
    projectedLoss_topLayer_activeStar_card
      C exponent huLoss huTop
  have hstarV :=
    projectedLoss_topLayer_activeStar_card
      C exponent hvLoss hvTop
  have hupper :=
    loss_activeStar_inter_activeStar_card_le_owner_sum
      C exponent hexp honeLoss huLoss hvLoss huv
  rw [hqU,hqV] at hupper
  have hambient :
      (activeStarCandidateBlock C u ∪
        activeStarCandidateBlock C v).card ≤ 2 ^ n := by
    have hsub :
        activeStarCandidateBlock C u ∪
            activeStarCandidateBlock C v
          ⊆
        (Finset.univ : Finset (Fin n → Bool)) := by
      intro word hword
      exact Finset.mem_univ _
    have hcard := Finset.card_le_card hsub
    simpa using hcard
  rw [Finset.card_union] at hambient
  rw [hstarU,hstarV] at hambient
  have hpowN :
      2 ^ n = 4 * 2 ^ (n - 2) := by
    have hs : n - 2 + 2 = n := by omega
    calc
      2 ^ n = 2 ^ (n - 2 + 2) := by rw [hs]
      _ = 2 ^ (n - 2) * 2 ^ 2 := by rw [pow_add]
      _ = 4 * 2 ^ (n - 2) := by ring
  have hpowNm1 :
      2 ^ (n - 1) = 2 * 2 ^ (n - 2) := by
    have hs : n - 2 + 1 = n - 1 := by omega
    calc
      2 ^ (n - 1) = 2 ^ (n - 2 + 1) := by rw [hs]
      _ = 2 ^ (n - 2) * 2 := by rw [pow_succ]
      _ = 2 * 2 ^ (n - 2) := by omega
  rw [hpowN] at hambient
  rw [hpowNm1]
  omega

theorem two_topLayer_lossStars_union_eq_univ
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexp : ∀ x, exponent x ≤ n)
    (honeLoss :
      ∀ x, (active C x).card ≤ n - exponent x + 1)
    {u v : V}
    (huLoss : u ∈ projectedLossVertices C exponent)
    (hvLoss : v ∈ projectedLossVertices C exponent)
    (huv : u ≠ v)
    (huTop : exponent u = n - 1)
    (hvTop : exponent v = n - 1) :
    activeStarCandidateBlock C u ∪
        activeStarCandidateBlock C v
      =
    (Finset.univ : Finset (Fin n → Bool)) := by
  classical
  apply Finset.eq_univ_of_card
  rw [Finset.card_union,
      projectedLoss_topLayer_activeStar_card
        C exponent huLoss huTop,
      projectedLoss_topLayer_activeStar_card
        C exponent hvLoss hvTop,
      two_topLayer_lossStars_intersection_card
        C exponent hexp honeLoss
        huLoss hvLoss huv huTop hvTop]
  have hn2 : 2 ≤ n := by
    have huEq :=
      (mem_projectedLossVertices C exponent u).1 huLoss
    unfold projectedFree at huEq
    omega
  have hpowN :
      2 ^ n = 4 * 2 ^ (n - 2) := by
    have hs : n - 2 + 2 = n := by omega
    calc
      2 ^ n = 2 ^ (n - 2 + 2) := by rw [hs]
      _ = 2 ^ (n - 2) * 2 ^ 2 := by rw [pow_add]
      _ = 4 * 2 ^ (n - 2) := by ring
  have hpowNm1 :
      2 ^ (n - 1) = 2 * 2 ^ (n - 2) := by
    have hs : n - 2 + 1 = n - 1 := by omega
    calc
      2 ^ (n - 1) = 2 ^ (n - 2 + 1) := by rw [hs]
      _ = 2 ^ (n - 2) * 2 := by rw [pow_succ]
      _ = 2 * 2 ^ (n - 2) := by omega
  simp only [Fintype.card_fun, Fintype.card_fin, Fintype.card_bool]
  rw [hpowN,hpowNm1]
  omega

#print axioms two_topLayer_lossStars_intersection_card
#print axioms two_topLayer_lossStars_union_eq_univ

end OrderedEdgeColoring
end JSP000404Research
