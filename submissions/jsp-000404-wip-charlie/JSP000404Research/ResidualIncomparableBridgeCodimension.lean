import JSP000404Research.ResidualIncomparableBridgePool
import Mathlib.Tactic

/-!
# Two distinct retained-active witnesses in every potential actual collision bridge

The actual-collision bridge palette obstruction is not just abstract
"incomparability": it forces TWO DIFFERENT Boolean coordinates.
One is active at the reverse-lower endpoint but not the forward-upper
endpoint, and the other is active at the forward-upper endpoint
but not the reverse-lower endpoint.

Because the overlap face is free only outside the union of endpoint
active palettes, all filtered candidate bridge overlap cubes
have codimension AT LEAST TWO. More precisely, the union exceeds
EACH endpoint palette by at least one coordinate. This is a genuine
uniform dimension gain, not a true-hole/surplus payment.
-/

namespace JSP000404Research
namespace OrderedEdgeColoring

/-- Incomparable finite retained palettes require two distinct
coordinate witnesses, oriented in opposite directions. -/
theorem incomparable_palettes_have_two_distinct_active_witnesses
    {V : Type*} [LinearOrder V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (u v : V)
    (hinc : ¬ retainedActive C u ⊆ retainedActive C v ∧
      ¬ retainedActive C v ⊆ retainedActive C u) :
    ∃ a b : Fin n,
      a ∈ retainedActive C u ∧
      a ∉ retainedActive C v ∧
      b ∈ retainedActive C v ∧
      b ∉ retainedActive C u ∧
      a ≠ b := by
  classical
  have ha : ∃ a : Fin n, a ∈ retainedActive C u ∧
      a ∉ retainedActive C v := by
    by_contra h
    apply hinc.1
    intro a ha
    by_contra hna
    exact h ⟨a, ha, hna⟩
  have hb : ∃ b : Fin n, b ∈ retainedActive C v ∧
      b ∉ retainedActive C u := by
    by_contra h
    apply hinc.2
    intro b hb
    by_contra hnb
    exact h ⟨b, hb, hnb⟩
  obtain ⟨a, haIn, haOut⟩ := ha
  obtain ⟨b, hbIn, hbOut⟩ := hb
  refine ⟨a, b, haIn, haOut, hbIn, hbOut, ?_⟩
  intro hab
  subst b
  exact haOut hbIn

/-- The union of incomparable active palettes contains at least two
distinct coordinates. This fails at n=0 or n=1. -/
theorem incomparable_palettes_union_card_ge_two
    {V : Type*} [LinearOrder V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (u v : V)
    (hinc : ¬ retainedActive C u ⊆ retainedActive C v ∧
      ¬ retainedActive C v ⊆ retainedActive C u) :
    2 ≤ (retainedActive C u ∪ retainedActive C v).card := by
  classical
  obtain ⟨a,b,haIn,_,hbIn,_,hne⟩ :=
    incomparable_palettes_have_two_distinct_active_witnesses
      C u v hinc
  have hpair :
      ({a,b} : Finset (Fin n)) ⊆
        retainedActive C u ∪ retainedActive C v := by
    intro c hc
    simp only [Finset.mem_insert, Finset.mem_singleton] at hc
    rcases hc with rfl | rfl
    · exact Finset.mem_union.mpr (Or.inl haIn)
    · exact Finset.mem_union.mpr (Or.inr hbIn)
  have hc := Finset.card_le_card hpair
  have htwo : ({a,b} : Finset (Fin n)).card = 2 := by
    simp [hne]
  omega

/-- Incomparability increases union cardinality by >= 1 relative
to EACH of its constituent active palettes. -/
theorem incomparable_palettes_strictly_expand_both
    {V : Type*} [LinearOrder V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (u v : V)
    (hinc : ¬ retainedActive C u ⊆ retainedActive C v ∧
      ¬ retainedActive C v ⊆ retainedActive C u) :
    (retainedActive C u).card + 1 ≤
        (retainedActive C u ∪ retainedActive C v).card ∧
      (retainedActive C v).card + 1 ≤
        (retainedActive C u ∪ retainedActive C v).card := by
  classical
  obtain ⟨a,b,haIn,haOut,hbIn,hbOut,_⟩ :=
    incomparable_palettes_have_two_distinct_active_witnesses
      C u v hinc
  constructor
  · have hsubset :
        insert b (retainedActive C u) ⊆
          retainedActive C u ∪ retainedActive C v := by
      intro c hc
      rcases Finset.mem_insert.mp hc with h | h
      · subst c
        exact Finset.mem_union.mpr (Or.inr hbIn)
      · exact Finset.mem_union.mpr (Or.inl h)
    have hcard := Finset.card_le_card hsubset
    simp [hbOut] at hcard
    omega
  · have hsubset :
        insert a (retainedActive C v) ⊆
          retainedActive C u ∪ retainedActive C v := by
      intro c hc
      rcases Finset.mem_insert.mp hc with h | h
      · subst c
        exact Finset.mem_union.mpr (Or.inl haIn)
      · exact Finset.mem_union.mpr (Or.inr h)
    have hcard := Finset.card_le_card hsubset
    simp [haOut] at hcard
    omega

/-- Relative to the ambient n-bit Boolean cube, the common inactive
palette has at most n-2 free coordinates for an incomparable pair. -/
theorem common_inactive_card_add_two_le_of_incomparable
    {V : Type*} [LinearOrder V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (u v : V)
    (hinc : ¬ retainedActive C u ⊆ retainedActive C v ∧
      ¬ retainedActive C v ⊆ retainedActive C u) :
    (commonRetainedInactive C u v).card + 2 ≤ n := by
  classical
  have htwo := incomparable_palettes_union_card_ge_two C u v hinc
  have hcard := commonRetainedInactive_card C u v
  have hbound :
      (retainedActive C u ∪ retainedActive C v).card ≤ n := by
    have hs := Finset.card_le_card
      (Finset.subset_univ (retainedActive C u ∪ retainedActive C v))
    simpa using hs
  omega

/-- The stronger one-coordinate loss relative to EITHER endpoint's
individual completion cube is also guaranteed. -/
theorem common_inactive_card_plus_each_active_lt_n
    {V : Type*} [LinearOrder V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (u v : V)
    (hinc : ¬ retainedActive C u ⊆ retainedActive C v ∧
      ¬ retainedActive C v ⊆ retainedActive C u) :
    (commonRetainedInactive C u v).card +
        (retainedActive C u).card + 1 ≤ n ∧
      (commonRetainedInactive C u v).card +
        (retainedActive C v).card + 1 ≤ n := by
  classical
  have hx := incomparable_palettes_strictly_expand_both C u v hinc
  have hc := commonRetainedInactive_card C u v
  have hbound :
      (retainedActive C u ∪ retainedActive C v).card ≤ n := by
    have hs := Finset.card_le_card
      (Finset.subset_univ (retainedActive C u ∪ retainedActive C v))
    simpa using hs
  omega

/-- Every filtered candidate soft-bridge face genuinely loses at
least two ambient Boolean dimensions. This is a true restriction on
the still eligible potential collision carrier set. -/
theorem incomparable_bridge_common_inactive_card_add_two_le
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (r : V × V)
    (hr : r ∈ incomparableBridgeSoftCarriers C exponent) :
    (commonRetainedInactive C r.1 r.2).card + 2 ≤ n := by
  have hinc := (Finset.mem_filter.mp hr).2
  exact common_inactive_card_add_two_le_of_incomparable
    C r.1 r.2 hinc

/-- Low dimensional case: there cannot be any filtered candidate
bridge if n<=1, independently of any geometric assumptions. -/
theorem incomparable_bridge_carriers_empty_of_n_le_one
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hn : n ≤ 1) :
    incomparableBridgeSoftCarriers C exponent = ∅ := by
  classical
  ext r
  constructor
  · intro hr
    have hcodim :=
      incomparable_bridge_common_inactive_card_add_two_le
        C exponent r hr
    omega
  · intro hr
    simpa using hr

/-- The actual cross-map collision set consequently vanishes
identically in ambient Boolean dimension n<=1. -/
theorem net_actual_collision_empty_of_n_le_one
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexp : ∀ v, exponent v ≤ n)
    (honeLoss : ∀ v, (active C v).card ≤ n - exponent v + 1)
    (hn : n ≤ 1) :
    netActualForwardReverseCollisionWords C exponent hexp honeLoss = ∅ := by
  classical
  ext word
  constructor
  · intro hw
    have hsubset := net_actual_collision_subset_incomparable_bridge_words
      C exponent hexp honeLoss hw
    obtain ⟨r, hr, _⟩ := Finset.mem_biUnion.mp hsubset
    have hnone := incomparable_bridge_carriers_empty_of_n_le_one
      C exponent hn
    rw [hnone] at hr
    simpa using hr
  · intro hw
    simpa using hw

#print axioms incomparable_palettes_have_two_distinct_active_witnesses
#print axioms incomparable_palettes_union_card_ge_two
#print axioms incomparable_palettes_strictly_expand_both
#print axioms common_inactive_card_add_two_le_of_incomparable
#print axioms common_inactive_card_plus_each_active_lt_n
#print axioms incomparable_bridge_common_inactive_card_add_two_le
#print axioms incomparable_bridge_carriers_empty_of_n_le_one
#print axioms net_actual_collision_empty_of_n_le_one

end OrderedEdgeColoring
end JSP000404Research
