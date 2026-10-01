import JSP000404Research.WeightedHallOutlet
import Mathlib.Tactic

/-!
# Block-level weighted Hall outlet

WeightedHallOutlet works with one candidate set for every dyadic target unit.
In the present residual projection, however, the natural geometric object is a
single Boolean candidate block B(v) attached to each vertex v, and all
2^k(v) target units of v may choose from that same block.

This file packages the exact reduction needed by the all-N proof.

Assume every finite vertex subset S satisfies

  sum_{v in S} 2^k(v) <= card (biUnion S B).

Then for every finite set of dyadic target units, its supporting vertex set has
enough block-union capacity.  Hall on the exploded dyadic units follows, hence

  sum_v 2^k(v) <= 2^n.

Thus the remaining global task can be stated purely as weighted expansion of
the vertex-level candidate blocks.
-/

namespace JSP000404Research

noncomputable def dyadicUnitSupport
    {V : Type*} [Fintype V]
    (exponent : V → ℕ)
    (s : Finset (DyadicTargetUnit exponent)) : Finset V := by
  classical
  exact s.image Sigma.fst

@[simp] theorem mem_dyadicUnitSupport
    {V : Type*} [Fintype V]
    (exponent : V → ℕ)
    (s : Finset (DyadicTargetUnit exponent))
    (v : V) :
    v ∈ dyadicUnitSupport exponent s ↔
      ∃ i : Fin (2 ^ exponent v), (⟨v,i⟩ : DyadicTargetUnit exponent) ∈ s := by
  classical
  constructor
  · intro hv
    rcases Finset.mem_image.mp hv with ⟨x,hxs,hxv⟩
    cases x with
    | mk w i =>
        dsimp at hxv
        subst w
        exact ⟨i,hxs⟩
  · rintro ⟨i,hi⟩
    apply Finset.mem_image.mpr
    exact ⟨⟨v,i⟩,hi,rfl⟩

theorem dyadicUnitSet_card_le_support_weight
    {V : Type*} [Fintype V]
    (exponent : V → ℕ)
    (s : Finset (DyadicTargetUnit exponent)) :
    s.card ≤
      ∑ v ∈ dyadicUnitSupport exponent s, 2 ^ exponent v := by
  classical
  let S := dyadicUnitSupport exponent s
  let f :
      {x : DyadicTargetUnit exponent // x ∈ s} →
      Sigma (fun v : {v : V // v ∈ S} => Fin (2 ^ exponent v.1)) :=
    fun x =>
      ⟨⟨x.1.1, by
          apply Finset.mem_image.mpr
          exact ⟨x.1,x.2,rfl⟩⟩,
        x.1.2⟩
  have hf : Function.Injective f := by
    intro x y hxy
    apply Subtype.ext
    cases x with
    | mk x hx =>
      cases y with
      | mk y hy =>
        cases x with
        | mk vx ix =>
          cases y with
          | mk vy iy =>
            simp only [f, Sigma.mk.inj_iff] at hxy
            rcases hxy with ⟨hvy,hiy⟩
            subst vy
            simp only [Sigma.mk.injEq] at hiy
            subst iy
            rfl
  have hcard :=
    Fintype.card_le_of_injective f hf
  have hdomain :
      Fintype.card {x : DyadicTargetUnit exponent // x ∈ s} =
        s.card := by
    simp
  have hcodomain :
      Fintype.card
        (Sigma (fun v : {v : V // v ∈ S} =>
          Fin (2 ^ exponent v.1)))
        =
      ∑ v ∈ S, 2 ^ exponent v := by
    rw [Fintype.card_sigma]
    simp
  rw [hdomain,hcodomain] at hcard
  exact hcard

theorem dyadicUnit_candidates_union_eq_support_blocks
    {V : Type*} [Fintype V]
    {n : ℕ}
    (exponent : V → ℕ)
    (blocks : V → Finset (Fin n → Bool))
    (s : Finset (DyadicTargetUnit exponent)) :
    s.biUnion (fun x => blocks x.1) =
      (dyadicUnitSupport exponent s).biUnion blocks := by
  classical
  ext word
  constructor
  · intro hw
    rcases Finset.mem_biUnion.mp hw with ⟨x,hxs,hword⟩
    apply Finset.mem_biUnion.mpr
    refine ⟨x.1,?_,hword⟩
    apply Finset.mem_image.mpr
    exact ⟨x,hxs,rfl⟩
  · intro hw
    rcases Finset.mem_biUnion.mp hw with ⟨v,hvS,hword⟩
    rcases Finset.mem_image.mp hvS with ⟨x,hxs,hxv⟩
    apply Finset.mem_biUnion.mpr
    refine ⟨x,hxs,?_⟩
    simpa [hxv] using hword

theorem dyadic_capacity_of_vertex_block_expansion
    {V : Type*} [Fintype V]
    {n : ℕ}
    (exponent : V → ℕ)
    (blocks : V → Finset (Fin n → Bool))
    (hExpansion :
      ∀ S : Finset V,
        (∑ v ∈ S, 2 ^ exponent v) ≤
          (S.biUnion blocks).card) :
    (∑ v : V, 2 ^ exponent v) ≤ 2 ^ n := by
  classical
  apply dyadic_capacity_of_hall_candidates
    exponent (fun x => blocks x.1)
  intro s
  have hsupport :=
    dyadicUnitSet_card_le_support_weight exponent s
  have hexpand :=
    hExpansion (dyadicUnitSupport exponent s)
  rw [dyadicUnit_candidates_union_eq_support_blocks
      exponent blocks s]
  exact hsupport.trans hexpand

theorem dyadic_capacity_of_exact_size_vertex_blocks
    {V : Type*} [Fintype V]
    {n : ℕ}
    (exponent : V → ℕ)
    (blocks : V → Finset (Fin n → Bool))
    (hsize : ∀ v, (blocks v).card = 2 ^ exponent v)
    (hExpansion :
      ∀ S : Finset V,
        (∑ v ∈ S, (blocks v).card) ≤
          (S.biUnion blocks).card) :
    (∑ v : V, 2 ^ exponent v) ≤ 2 ^ n := by
  apply dyadic_capacity_of_vertex_block_expansion
    exponent blocks
  intro S
  calc
    (∑ v ∈ S, 2 ^ exponent v)
        = ∑ v ∈ S, (blocks v).card := by
            apply Finset.sum_congr rfl
            intro v hv
            symm
            exact hsize v
    _ ≤ (S.biUnion blocks).card := hExpansion S

#print axioms dyadicUnitSet_card_le_support_weight
#print axioms dyadicUnit_candidates_union_eq_support_blocks
#print axioms dyadic_capacity_of_vertex_block_expansion
#print axioms dyadic_capacity_of_exact_size_vertex_blocks

end JSP000404Research
