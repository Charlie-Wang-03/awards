import JSP000404Research.MinimalBlockPrivateDeficit
import Mathlib.Tactic

/-!
# Quantitative shared-word lower bound in a minimal Hall obstruction

For v in a minimal deficient block family, split B(v) into

  private(v) = B(v) \ union(others),
  shared(v)  = B(v) ∩ union(others).

These two pieces partition B(v).  Minimal deficiency gives

  card private(v) < demand(v).

If local capacity holds, demand(v) <= card B(v), then

  card B(v) - demand(v) + 1 <= card shared(v).

Thus every unit of local slack, plus one additional unit witnessing the Hall
defect, is forced into collisions with the other candidate blocks.
-/

namespace JSP000404Research

noncomputable def sharedBlockWords
    {V W : Type*} [DecidableEq V] [DecidableEq W]
    (blocks : V → Finset W)
    (T : Finset V)
    (v : V) : Finset W :=
  blocks v ∩ (T.erase v).biUnion blocks

theorem private_union_shared_eq_block
    {V W : Type*} [Fintype V] [DecidableEq V] [DecidableEq W]
    (blocks : V → Finset W)
    (T : Finset V)
    (v : V) :
    privateBlockWords blocks T v ∪
      sharedBlockWords blocks T v =
    blocks v := by
  classical
  unfold privateBlockWords sharedBlockWords
  exact Finset.sdiff_union_inter
    (blocks v) ((T.erase v).biUnion blocks)

theorem private_disjoint_shared
    {V W : Type*} [Fintype V] [DecidableEq V] [DecidableEq W]
    (blocks : V → Finset W)
    (T : Finset V)
    (v : V) :
    Disjoint
      (privateBlockWords blocks T v)
      (sharedBlockWords blocks T v) := by
  classical
  rw [Finset.disjoint_left]
  intro w hwPrivate hwShared
  have hp := Finset.mem_sdiff.mp hwPrivate
  have hs := Finset.mem_inter.mp hwShared
  exact hp.2 hs.2

theorem block_card_eq_private_add_shared
    {V W : Type*} [Fintype V] [DecidableEq V] [DecidableEq W]
    (blocks : V → Finset W)
    (T : Finset V)
    (v : V) :
    (blocks v).card =
      (privateBlockWords blocks T v).card +
        (sharedBlockWords blocks T v).card := by
  rw [← private_union_shared_eq_block blocks T v,
      Finset.card_union_of_disjoint
        (private_disjoint_shared blocks T v)]

theorem minimal_deficient_shared_card_ge_slack_add_one
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
    (blocks v).card - demand v + 1 ≤
      (sharedBlockWords blocks T v).card := by
  have hprivate :=
    minimal_deficient_private_card_lt_demand
      demand blocks hdef hmin hv
  have hsplit :=
    block_card_eq_private_add_shared blocks T v
  omega

theorem minimal_deficient_exact_block_has_shared_word
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
    (hexact : (blocks v).card = demand v) :
    (sharedBlockWords blocks T v).Nonempty := by
  have hbound :=
    minimal_deficient_shared_card_ge_slack_add_one
      demand blocks hdef hmin hv
      (by omega)
  rw [hexact] at hbound
  have hpos : 0 < (sharedBlockWords blocks T v).card := by
    omega
  exact Finset.card_pos.mp hpos


def blockDeficiencyAmount
    {V W : Type*} [DecidableEq V] [DecidableEq W]
    (demand : V → ℕ)
    (blocks : V → Finset W)
    (T : Finset V) : ℕ :=
  (∑ v ∈ T, demand v) - (T.biUnion blocks).card

theorem blockDeficiencyAmount_pos_of_deficient
    {V W : Type*} [DecidableEq V] [DecidableEq W]
    (demand : V → ℕ)
    (blocks : V → Finset W)
    {T : Finset V}
    (hdef : BlockDeficient demand blocks T) :
    0 < blockDeficiencyAmount demand blocks T := by
  unfold BlockDeficient at hdef
  unfold blockDeficiencyAmount
  omega

theorem minimal_deficient_amount_le_shared_minus_slack
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
    blockDeficiencyAmount demand blocks T ≤
      (sharedBlockWords blocks T v).card -
        ((blocks v).card - demand v) := by
  classical
  have hdelete :=
    minimal_deficient_delete_recovers
      demand blocks hdef hmin v hv
  have hprivate :=
    minimal_deficient_private_card_lt_demand
      demand blocks hdef hmin hv
  have hsplit :=
    block_card_eq_private_add_shared blocks T v

  have hUnionSplit :
      (T.biUnion blocks).card =
        ((T.erase v).biUnion blocks).card +
          (privateBlockWords blocks T v).card := by
    have hdisj :
        Disjoint
          ((T.erase v).biUnion blocks)
          (privateBlockWords blocks T v) := by
      rw [Finset.disjoint_left]
      intro w hwOthers hwPrivate
      exact (Finset.mem_sdiff.mp hwPrivate).2 hwOthers
    have hEq :
        T.biUnion blocks =
          (T.erase v).biUnion blocks ∪
            privateBlockWords blocks T v := by
      ext w
      constructor
      · intro hwT
        obtain ⟨u,huT,huW⟩ := Finset.mem_biUnion.mp hwT
        by_cases huv : u = v
        · subst u
          by_cases hwOther :
              w ∈ (T.erase v).biUnion blocks
          · exact Finset.mem_union_left _ hwOther
          · apply Finset.mem_union_right
            exact Finset.mem_sdiff.mpr ⟨huW,hwOther⟩
        · apply Finset.mem_union_left
          apply Finset.mem_biUnion.mpr
          exact ⟨u,Finset.mem_erase.mpr ⟨huv,huT⟩,huW⟩
      · intro hw
        rcases Finset.mem_union.mp hw with hwOther | hwPrivate
        · obtain ⟨u,huErase,huW⟩ := Finset.mem_biUnion.mp hwOther
          apply Finset.mem_biUnion.mpr
          exact ⟨u,(Finset.mem_erase.mp huErase).2,huW⟩
        · have hwBlock := (Finset.mem_sdiff.mp hwPrivate).1
          apply Finset.mem_biUnion.mpr
          exact ⟨v,hv,hwBlock⟩
    rw [hEq, Finset.card_union_of_disjoint hdisj]

  have hSumSplit :
      (∑ u ∈ T, demand u) =
        (∑ u ∈ T.erase v, demand u) + demand v := by
    rw [← Finset.sum_erase_add _ _ hv]

  unfold blockDeficiencyAmount
  rw [hUnionSplit,hSumSplit]
  have hslackEq :
      (blocks v).card - demand v =
        (sharedBlockWords blocks T v).card -
          (demand v - (privateBlockWords blocks T v).card) := by
    omega
  omega

theorem minimal_deficient_amount_le_shared_excess
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
    blockDeficiencyAmount demand blocks T +
        ((blocks v).card - demand v)
      ≤
    (sharedBlockWords blocks T v).card := by
  have h :=
    minimal_deficient_amount_le_shared_minus_slack
      demand blocks hdef hmin hv hlocal
  have hslackLe :
      (blocks v).card - demand v ≤
        (sharedBlockWords blocks T v).card := by
    have hpos :=
      blockDeficiencyAmount_pos_of_deficient
        demand blocks hdef
    omega
  omega


noncomputable def deletedVertexTransfer
    {V W : Type*} [DecidableEq V] [DecidableEq W]
    (demand : V → ℕ)
    (blocks : V → Finset W)
    (T : Finset V)
    (v : V) : ℕ :=
  demand v - (privateBlockWords blocks T v).card

def addDemandAt
    {V : Type*} [DecidableEq V]
    (demand : V → ℕ)
    (w : V)
    (r : ℕ) : V → ℕ :=
  fun x => if x = w then demand x + r else demand x

theorem minimal_deficient_deletedVertexTransfer_pos
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
    0 < deletedVertexTransfer demand blocks T v := by
  have hprivate :=
    minimal_deficient_private_card_lt_demand
      demand blocks hdef hmin hv
  unfold deletedVertexTransfer
  omega

theorem deletedVertexTransfer_eq_shared_minus_slack
    {V W : Type*} [Fintype V] [DecidableEq V] [DecidableEq W]
    (demand : V → ℕ)
    (blocks : V → Finset W)
    (T : Finset V)
    (v : V)
    (hlocal : demand v ≤ (blocks v).card) :
    deletedVertexTransfer demand blocks T v =
      (sharedBlockWords blocks T v).card -
        ((blocks v).card - demand v) := by
  have hsplit :=
    block_card_eq_private_add_shared blocks T v
  unfold deletedVertexTransfer
  omega

theorem biUnion_card_eq_delete_add_private
    {V W : Type*} [Fintype V] [DecidableEq V] [DecidableEq W]
    (blocks : V → Finset W)
    {T : Finset V}
    {v : V}
    (hv : v ∈ T) :
    (T.biUnion blocks).card =
      ((T.erase v).biUnion blocks).card +
        (privateBlockWords blocks T v).card := by
  classical
  have hdisj :
      Disjoint
        ((T.erase v).biUnion blocks)
        (privateBlockWords blocks T v) := by
    rw [Finset.disjoint_left]
    intro w hwOthers hwPrivate
    exact (Finset.mem_sdiff.mp hwPrivate).2 hwOthers
  have hEq :
      T.biUnion blocks =
        (T.erase v).biUnion blocks ∪
          privateBlockWords blocks T v := by
    ext w
    constructor
    · intro hwT
      obtain ⟨u,huT,huW⟩ := Finset.mem_biUnion.mp hwT
      by_cases huv : u = v
      · subst u
        by_cases hwOther :
            w ∈ (T.erase v).biUnion blocks
        · exact Finset.mem_union_left _ hwOther
        · apply Finset.mem_union_right
          exact Finset.mem_sdiff.mpr ⟨huW,hwOther⟩
      · apply Finset.mem_union_left
        apply Finset.mem_biUnion.mpr
        exact ⟨u,Finset.mem_erase.mpr ⟨huv,huT⟩,huW⟩
    · intro hw
      rcases Finset.mem_union.mp hw with hwOther | hwPrivate
      · obtain ⟨u,huErase,huW⟩ := Finset.mem_biUnion.mp hwOther
        apply Finset.mem_biUnion.mpr
        exact ⟨u,(Finset.mem_erase.mp huErase).2,huW⟩
      · have hwBlock := (Finset.mem_sdiff.mp hwPrivate).1
        apply Finset.mem_biUnion.mpr
        exact ⟨v,hv,hwBlock⟩
  rw [hEq, Finset.card_union_of_disjoint hdisj]

theorem sum_addDemandAt
    {V : Type*} [DecidableEq V]
    (demand : V → ℕ)
    (S : Finset V)
    {w : V}
    (hw : w ∈ S)
    (r : ℕ) :
    (∑ x ∈ S, addDemandAt demand w r x) =
      (∑ x ∈ S, demand x) + r := by
  classical
  have hpoint :
      ∀ x ∈ S,
        addDemandAt demand w r x =
          demand x + (if x = w then r else 0) := by
    intro x hx
    by_cases h : x = w <;> simp [addDemandAt, h]
  calc
    (∑ x ∈ S, addDemandAt demand w r x)
      =
    ∑ x ∈ S, (demand x + (if x = w then r else 0)) := by
      apply Finset.sum_congr rfl
      intro x hx
      exact hpoint x hx
    _ =
      (∑ x ∈ S, demand x) +
        ∑ x ∈ S, (if x = w then r else 0) := by
      rw [Finset.sum_add_distrib]
    _ =
      (∑ x ∈ S, demand x) + r := by
      rw [Finset.sum_ite_eq' S w (fun _ => r)]
      simp [hw]

theorem minimal_deficient_delete_with_transfer_deficient
    {V W : Type*} [Fintype V] [DecidableEq V] [DecidableEq W]
    (demand : V → ℕ)
    (blocks : V → Finset W)
    {T : Finset V}
    (hdef : BlockDeficient demand blocks T)
    (hmin :
      ∀ U : Finset V,
        U ⊂ T →
        ¬ BlockDeficient demand blocks U)
    {v w : V}
    (hv : v ∈ T)
    (hw : w ∈ T.erase v) :
    BlockDeficient
      (addDemandAt demand w
        (deletedVertexTransfer demand blocks T v))
      blocks
      (T.erase v) := by
  classical
  have hprivate :=
    minimal_deficient_private_card_lt_demand
      demand blocks hdef hmin hv
  have hUnion :=
    biUnion_card_eq_delete_add_private
      blocks hv
  have hSum :
      (∑ x ∈ T, demand x) =
        (∑ x ∈ T.erase v, demand x) + demand v := by
    rw [← Finset.sum_erase_add _ _ hv]
  have hTransfer :
      deletedVertexTransfer demand blocks T v +
          (privateBlockWords blocks T v).card =
        demand v := by
    unfold deletedVertexTransfer
    omega
  unfold BlockDeficient at hdef ⊢
  rw [sum_addDemandAt demand (T.erase v) hw]
  rw [hUnion,hSum] at hdef
  omega


theorem deficient_delete_with_transfer_deficient
    {V W : Type*} [Fintype V] [DecidableEq V] [DecidableEq W]
    (demand : V → ℕ)
    (blocks : V → Finset W)
    {T : Finset V}
    (hdef : BlockDeficient demand blocks T)
    {v w : V}
    (hv : v ∈ T)
    (hw : w ∈ T.erase v) :
    BlockDeficient
      (addDemandAt demand w
        (deletedVertexTransfer demand blocks T v))
      blocks
      (T.erase v) := by
  classical
  have hUnion :=
    biUnion_card_eq_delete_add_private
      blocks hv
  have hSum :
      (∑ x ∈ T, demand x) =
        (∑ x ∈ T.erase v, demand x) + demand v := by
    rw [← Finset.sum_erase_add _ _ hv]
  unfold BlockDeficient at hdef ⊢
  rw [sum_addDemandAt demand (T.erase v) hw]
  rw [hUnion,hSum] at hdef
  unfold deletedVertexTransfer
  omega

theorem minimal_deficient_delete_with_transfer_deficient'
    {V W : Type*} [Fintype V] [DecidableEq V] [DecidableEq W]
    (demand : V → ℕ)
    (blocks : V → Finset W)
    {T : Finset V}
    (hdef : BlockDeficient demand blocks T)
    (hmin :
      ∀ U : Finset V,
        U ⊂ T →
        ¬ BlockDeficient demand blocks U)
    {v w : V}
    (hv : v ∈ T)
    (hw : w ∈ T.erase v) :
    BlockDeficient
      (addDemandAt demand w
        (deletedVertexTransfer demand blocks T v))
      blocks
      (T.erase v) :=
  deficient_delete_with_transfer_deficient
    demand blocks hdef hv hw


theorem blockDeficiencyAmount_le_delete_with_transfer
    {V W : Type*} [Fintype V] [DecidableEq V] [DecidableEq W]
    (demand : V → ℕ)
    (blocks : V → Finset W)
    {T : Finset V}
    {v w : V}
    (hv : v ∈ T)
    (hw : w ∈ T.erase v) :
    blockDeficiencyAmount demand blocks T ≤
      blockDeficiencyAmount
        (addDemandAt demand w
          (deletedVertexTransfer demand blocks T v))
        blocks
        (T.erase v) := by
  classical
  have hUnion :=
    biUnion_card_eq_delete_add_private
      blocks hv
  have hSum :
      (∑ x ∈ T, demand x) =
        (∑ x ∈ T.erase v, demand x) + demand v := by
    rw [← Finset.sum_erase_add _ _ hv]
  unfold blockDeficiencyAmount
  rw [sum_addDemandAt demand (T.erase v) hw]
  rw [hUnion,hSum]
  unfold deletedVertexTransfer
  omega

theorem blockDeficiencyAmount_delete_with_transfer_eq_of_private_le
    {V W : Type*} [Fintype V] [DecidableEq V] [DecidableEq W]
    (demand : V → ℕ)
    (blocks : V → Finset W)
    {T : Finset V}
    {v w : V}
    (hv : v ∈ T)
    (hw : w ∈ T.erase v)
    (hprivate :
      (privateBlockWords blocks T v).card ≤ demand v) :
    blockDeficiencyAmount
      (addDemandAt demand w
        (deletedVertexTransfer demand blocks T v))
      blocks
      (T.erase v)
      =
    blockDeficiencyAmount demand blocks T := by
  classical
  have hUnion :=
    biUnion_card_eq_delete_add_private
      blocks hv
  have hSum :
      (∑ x ∈ T, demand x) =
        (∑ x ∈ T.erase v, demand x) + demand v := by
    rw [← Finset.sum_erase_add _ _ hv]
  unfold blockDeficiencyAmount
  rw [sum_addDemandAt demand (T.erase v) hw]
  rw [hUnion,hSum]
  unfold deletedVertexTransfer
  omega

theorem minimal_deficient_delete_with_transfer_preserves_amount
    {V W : Type*} [Fintype V] [DecidableEq V] [DecidableEq W]
    (demand : V → ℕ)
    (blocks : V → Finset W)
    {T : Finset V}
    (hdef : BlockDeficient demand blocks T)
    (hmin :
      ∀ U : Finset V,
        U ⊂ T →
        ¬ BlockDeficient demand blocks U)
    {v w : V}
    (hv : v ∈ T)
    (hw : w ∈ T.erase v) :
    BlockDeficient
      (addDemandAt demand w
        (deletedVertexTransfer demand blocks T v))
      blocks
      (T.erase v)
    ∧
    blockDeficiencyAmount
      (addDemandAt demand w
        (deletedVertexTransfer demand blocks T v))
      blocks
      (T.erase v)
      =
    blockDeficiencyAmount demand blocks T := by
  have hprivate :
      (privateBlockWords blocks T v).card ≤ demand v := by
    have hlt :=
      minimal_deficient_private_card_lt_demand
        demand blocks hdef hmin hv
    omega
  exact ⟨
    deficient_delete_with_transfer_deficient
      demand blocks hdef hv hw,
    blockDeficiencyAmount_delete_with_transfer_eq_of_private_le
      demand blocks hv hw hprivate
  ⟩

#print axioms blockDeficiencyAmount_pos_of_deficient
#print axioms deficient_delete_with_transfer_deficient
#print axioms blockDeficiencyAmount_le_delete_with_transfer
#print axioms blockDeficiencyAmount_delete_with_transfer_eq_of_private_le
#print axioms minimal_deficient_delete_with_transfer_preserves_amount

end JSP000404Research
