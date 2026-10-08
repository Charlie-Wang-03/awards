import JSP000404Research.MinimalBlockDeficiency
import Mathlib.Tactic

/-!
# Private-word deficit inside a minimal Hall obstruction

Let T be an inclusion-minimal deficient vertex set for a block family B with
integer demands d.

For v in T define the private part of B(v) relative to the other vertices:

  private(v,T) = B(v) \ union_{u in T.erase v} B(u).

Deleting v restores Hall expansion by minimality.  Therefore v cannot
contribute d(v) or more private words; otherwise adding v back would preserve
expansion. Hence

  card private(v,T) < d(v).

Equivalently, every vertex in a minimal Hall obstruction must lose at least
one unit of its local target capacity to collisions with the other blocks.
-/

namespace JSP000404Research

noncomputable def privateBlockWords
    {V W : Type*} [DecidableEq V] [DecidableEq W]
    (blocks : V → Finset W)
    (T : Finset V)
    (v : V) : Finset W :=
  blocks v \ (T.erase v).biUnion blocks

theorem biUnion_eq_private_union_erase
    {V W : Type*} [Fintype V] [DecidableEq V] [DecidableEq W]
    (blocks : V → Finset W)
    {T : Finset V} {v : V}
    (hv : v ∈ T) :
    T.biUnion blocks =
      privateBlockWords blocks T v ∪
        (T.erase v).biUnion blocks := by
  classical
  classical
  ext w
  simp only [privateBlockWords, Finset.mem_union, Finset.mem_sdiff,
    Finset.mem_biUnion]
  constructor
  · rintro ⟨u, huT, hwU⟩
    by_cases huv : u = v
    · subst u
      by_cases hwOther : ∃ x ∈ T.erase v, w ∈ blocks x
      · exact Or.inr hwOther
      · exact Or.inl ⟨hwU, hwOther⟩
    · exact Or.inr ⟨u, Finset.mem_erase.mpr ⟨huv, huT⟩, hwU⟩
  · rintro (⟨hwV, _⟩ | ⟨u, huErase, hwU⟩)
    · exact ⟨v, hv, hwV⟩
    · exact ⟨u, Finset.mem_of_mem_erase huErase, hwU⟩

theorem privateBlockWords_disjoint_eraseUnion
    {V W : Type*} [Fintype V] [DecidableEq V] [DecidableEq W]
    (blocks : V → Finset W)
    (T : Finset V)
    (v : V) :
    Disjoint
      (privateBlockWords blocks T v)
      ((T.erase v).biUnion blocks) := by
  classical
  exact Finset.sdiff_disjoint

theorem minimal_deficient_private_card_lt_demand
    {V W : Type*} [Fintype V] [DecidableEq V] [DecidableEq W]
    (demand : V → ℕ)
    (blocks : V → Finset W)
    {T : Finset V}
    (hdef : BlockDeficient demand blocks T)
    (hmin :
      ∀ U : Finset V,
        U ⊂ T →
        ¬ BlockDeficient demand blocks U)
    {v : V}
    (hv : v ∈ T) :
    (privateBlockWords blocks T v).card < demand v := by
  classical
  have hdel :=
    minimal_deficient_delete_recovers
      demand blocks hdef hmin v hv
  have hsplitT :
      T = insert v (T.erase v) := by
    symm
    exact Finset.insert_erase hv
  have hsum :
      (∑ u ∈ T, demand u) =
        demand v + ∑ u ∈ T.erase v, demand u := by
    rw [hsplitT]
    simp
  have hunion :
      (T.biUnion blocks).card =
        (privateBlockWords blocks T v).card +
          ((T.erase v).biUnion blocks).card := by
    rw [biUnion_eq_private_union_erase blocks hv,
        Finset.card_union_of_disjoint
          (privateBlockWords_disjoint_eraseUnion blocks T v)]
  unfold BlockDeficient at hdef
  rw [hsum,hunion] at hdef
  omega

/--
A quantitative form of collision pressure in an inclusion-minimal Hall
obstruction: the full local block is strictly smaller than its demand plus
the number of words shared with other vertices of the deficient core.

Unlike the existence-of-a-collision corollary, this remains informative
when the local block has many more words than its demand.
-/
theorem minimal_deficient_local_block_lt_demand_add_shared
    {V W : Type*} [Fintype V] [DecidableEq V] [DecidableEq W]
    (demand : V → ℕ)
    (blocks : V → Finset W)
    {T : Finset V}
    (hdef : BlockDeficient demand blocks T)
    (hmin :
      ∀ U : Finset V,
        U ⊂ T →
        ¬ BlockDeficient demand blocks U)
    {v : V}
    (hv : v ∈ T) :
    (blocks v).card <
      demand v +
        (blocks v ∩ (T.erase v).biUnion blocks).card := by
  classical
  let other : Finset W := (T.erase v).biUnion blocks
  have hsplit :
      blocks v = privateBlockWords blocks T v ∪
        (blocks v ∩ other) := by
    ext w
    simp only [privateBlockWords, Finset.mem_union,
      Finset.mem_sdiff, Finset.mem_inter]
    tauto
  have hdisj :
      Disjoint (privateBlockWords blocks T v)
        (blocks v ∩ other) := by
    apply Finset.disjoint_left.mpr
    intro w hwPrivate hwShared
    have hwNotOther : w ∉ other :=
      (Finset.mem_sdiff.mp hwPrivate).2
    exact hwNotOther (Finset.mem_inter.mp hwShared).2
  have hcard :
      (blocks v).card =
        (privateBlockWords blocks T v).card +
          (blocks v ∩ other).card := by
    rw [hsplit, Finset.card_union_of_disjoint hdisj]
  have hprivate :=
    minimal_deficient_private_card_lt_demand
      demand blocks hdef hmin hv
  dsimp [other] at hcard ⊢
  omega

theorem minimal_deficient_block_has_collision_of_local_capacity
    {V W : Type*} [Fintype V] [DecidableEq V] [DecidableEq W]
    (demand : V → ℕ)
    (blocks : V → Finset W)
    {T : Finset V}
    (hdef : BlockDeficient demand blocks T)
    (hmin :
      ∀ U : Finset V,
        U ⊂ T →
        ¬ BlockDeficient demand blocks U)
    {v : V}
    (hv : v ∈ T)
    (hlocal : demand v ≤ (blocks v).card) :
    ∃ w : W,
      w ∈ blocks v ∧
      w ∈ (T.erase v).biUnion blocks := by
  classical
  by_contra hnone
  push_neg at hnone
  have hprivateEq :
      privateBlockWords blocks T v = blocks v := by
    apply Finset.ext
    intro w
    simp only [privateBlockWords, Finset.mem_sdiff]
    constructor
    · intro hw
      exact hw.1
    · intro hw
      exact ⟨hw, hnone w hw⟩
  have hlt :=
    minimal_deficient_private_card_lt_demand
      demand blocks hdef hmin hv
  rw [hprivateEq] at hlt
  omega

#print axioms biUnion_eq_private_union_erase
#print axioms minimal_deficient_private_card_lt_demand
#print axioms minimal_deficient_local_block_lt_demand_add_shared
#print axioms minimal_deficient_block_has_collision_of_local_capacity

end JSP000404Research
