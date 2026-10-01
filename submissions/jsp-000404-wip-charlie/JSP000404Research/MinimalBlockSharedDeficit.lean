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
  ext w
  simp [privateBlockWords, sharedBlockWords]
  tauto

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

#print axioms block_card_eq_private_add_shared
#print axioms minimal_deficient_shared_card_ge_slack_add_one
#print axioms minimal_deficient_exact_block_has_shared_word

end JSP000404Research
