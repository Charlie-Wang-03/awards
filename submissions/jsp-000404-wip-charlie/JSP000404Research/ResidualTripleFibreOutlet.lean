import JSP000404Research.ResidualBoundedMultiplicityAccounting
import JSP000404Research.ResidualEnlargedTriangleOutlet
import Mathlib.Tactic

/-!
# Triple-fibre outlet for deficient enlarged-candidate cores

A Boolean word of core multiplicity at least three determines three distinct
core vertices carrying that same word.  Those vertices form a collision
triangle automatically.

Combining this with the bounded-multiplicity accounting dichotomy removes the
need to split first on graph girth.  Every deficient core now yields either

* an exact/top-loss shared-mass overload, or
* a genuine triple-covered word and its collision triangle.

The triangle can then be fed directly into the previously established
deep/high-layer-loss-pair / paid / exact-recursive reduction.
-/

namespace JSP000404Research
namespace OrderedEdgeColoring

theorem tripleFibre_has_common_word_collision_triangle
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    {T : Finset V}
    {word : Fin n → Bool}
    (hthree :
      3 ≤ (coreEnlargedCandidateFibre
        C exponent T word).card) :
    ∃ u v w : {x : V // x ∈ T},
      u ≠ v ∧
      u ≠ w ∧
      v ≠ w ∧
      word ∈ enlargedProjectedCandidateBlock C exponent u.1 ∧
      word ∈ enlargedProjectedCandidateBlock C exponent v.1 ∧
      word ∈ enlargedProjectedCandidateBlock C exponent w.1 ∧
      (enlargedCollisionGraph C exponent T).Adj u v ∧
      (enlargedCollisionGraph C exponent T).Adj u w ∧
      (enlargedCollisionGraph C exponent T).Adj v w := by
  classical
  obtain ⟨S,hSsub,hScard⟩ :=
    Finset.exists_subset_card_eq hthree
  have hScard3 : S.card = 3 := hScard
  obtain ⟨u0,v0,w0,huv,huw,hvw,hSeq⟩ :=
    Finset.card_eq_three.mp hScard3
  subst S

  have huF :
      u0 ∈ coreEnlargedCandidateFibre C exponent T word :=
    hSsub (by simp)
  have hvF :
      v0 ∈ coreEnlargedCandidateFibre C exponent T word :=
    hSsub (by simp)
  have hwF :
      w0 ∈ coreEnlargedCandidateFibre C exponent T word :=
    hSsub (by simp)

  have huData :=
    (mem_coreEnlargedCandidateFibre
      C exponent T word u0).1 huF
  have hvData :=
    (mem_coreEnlargedCandidateFibre
      C exponent T word v0).1 hvF
  have hwData :=
    (mem_coreEnlargedCandidateFibre
      C exponent T word w0).1 hwF

  let u : {x : V // x ∈ T} := ⟨u0,huData.1⟩
  let v : {x : V // x ∈ T} := ⟨v0,hvData.1⟩
  let w : {x : V // x ∈ T} := ⟨w0,hwData.1⟩

  have huvSub : u ≠ v := by
    intro h
    apply huv
    exact congrArg Subtype.val h
  have huwSub : u ≠ w := by
    intro h
    apply huw
    exact congrArg Subtype.val h
  have hvwSub : v ≠ w := by
    intro h
    apply hvw
    exact congrArg Subtype.val h

  have hUV :
      (enlargedCollisionGraph C exponent T).Adj u v := by
    apply enlargedCollisionGraph_adj_of_cross
      C exponent T huData.1 hvData.1 huv
    exact ⟨word,huData.2,hvData.2⟩
  have hUW :
      (enlargedCollisionGraph C exponent T).Adj u w := by
    apply enlargedCollisionGraph_adj_of_cross
      C exponent T huData.1 hwData.1 huw
    exact ⟨word,huData.2,hwData.2⟩
  have hVW :
      (enlargedCollisionGraph C exponent T).Adj v w := by
    apply enlargedCollisionGraph_adj_of_cross
      C exponent T hvData.1 hwData.1 hvw
    exact ⟨word,hvData.2,hwData.2⟩

  exact ⟨u,v,w,huvSub,huwSub,hvwSub,
    huData.2,hvData.2,hwData.2,hUV,hUW,hVW⟩

theorem deficientCore_tripleWord_or_exactTopLossOverload
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexpLt : ∀ x, exponent x < n)
    (hexp : ∀ x, exponent x ≤ n)
    (honeLoss :
      ∀ x, (active C x).card ≤ n - exponent x + 1)
    {T : Finset V}
    (hdef :
      BlockDeficient
        (fun x => 2 ^ exponent x)
        (enlargedProjectedCandidateBlock C exponent)
        T) :
    (
      ∃ word : Fin n → Bool,
        ∃ u v w : {x : V // x ∈ T},
          u ≠ v ∧
          u ≠ w ∧
          v ≠ w ∧
          word ∈ enlargedProjectedCandidateBlock C exponent u.1 ∧
          word ∈ enlargedProjectedCandidateBlock C exponent v.1 ∧
          word ∈ enlargedProjectedCandidateBlock C exponent w.1 ∧
          (enlargedCollisionGraph C exponent T).Adj u v ∧
          (enlargedCollisionGraph C exponent T).Adj u w ∧
          (enlargedCollisionGraph C exponent T).Adj v w
    )
    ∨
    (
      ∃ v ∈ T,
        (
          ExactProjectedBudget C exponent v
          ∨
          (v ∈ projectedLossVertices C exponent ∧
            exponent v = n - 1)
        )
        ∧
        2 *
          ((enlargedProjectedCandidateBlock C exponent v).card -
            2 ^ exponent v)
          <
        (sharedBlockWords
          (enlargedProjectedCandidateBlock C exponent)
          T v).card
    ) := by
  rcases
    deficientCore_tripleFibre_or_exactTopLossOverload
      C exponent hexpLt hexp honeLoss hdef
    with htriple | hover
  · obtain ⟨word,hthree⟩ := htriple
    obtain ⟨u,v,w,huv,huw,hvw,
      huWord,hvWord,hwWord,hUV,hUW,hVW⟩ :=
      tripleFibre_has_common_word_collision_triangle
        C exponent hthree
    exact Or.inl
      ⟨word,u,v,w,huv,huw,hvw,
        huWord,hvWord,hwWord,hUV,hUW,hVW⟩
  · exact Or.inr hover

theorem deficientCore_deep_or_highLossPair_or_paid_or_exactRecursive_or_topOverload
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexpLt : ∀ x, exponent x < n)
    (hexp : ∀ x, exponent x ≤ n)
    (honeLoss :
      ∀ x, (active C x).card ≤ n - exponent x + 1)
    (htop :
      ((Finset.univ : Finset V).filter
        (fun z => exponent z = n - 1)).card ≤ 1)
    {T : Finset V}
    (hdef :
      BlockDeficient
        (fun x => 2 ^ exponent x)
        (enlargedProjectedCandidateBlock C exponent)
        T) :
    (
      ∃ z : V,
        z ∈ projectedLossVertices C exponent ∧
        exponent z + 3 ≤ n
    )
    ∨
    (
      ∃ a b : {x : V // x ∈ T},
        a ≠ b ∧
        a.1 ∈ projectedLossVertices C exponent ∧
        b.1 ∈ projectedLossVertices C exponent ∧
        (
          (exponent a.1 = n - 1 ∧ exponent b.1 = n - 2)
          ∨
          (exponent a.1 = n - 2 ∧ exponent b.1 = n - 1)
          ∨
          (exponent a.1 = n - 2 ∧ exponent b.1 = n - 2)
        )
    )
    ∨
    (
      ∃ z : V,
        1 ≤ dyadicProfileSurplus
          exponent (projectedFree C) z
    )
    ∨
    (
      ∃ source : V,
        ExactRecursiveOutlet C exponent source
    )
    ∨
    (
      ∃ v ∈ T,
        (
          ExactProjectedBudget C exponent v
          ∨
          (v ∈ projectedLossVertices C exponent ∧
            exponent v = n - 1)
        )
        ∧
        2 *
          ((enlargedProjectedCandidateBlock C exponent v).card -
            2 ^ exponent v)
          <
        (sharedBlockWords
          (enlargedProjectedCandidateBlock C exponent)
          T v).card
    ) := by
  rcases
    deficientCore_tripleWord_or_exactTopLossOverload
      C exponent hexpLt hexp honeLoss hdef
    with htriple | hover
  · obtain ⟨word,u,v,w,_huv,_huw,_hvw,
      _huWord,_hvWord,_hwWord,hUV,hUW,hVW⟩ := htriple
    rcases
      enlargedCollisionGraph_triangle_deep_or_highPair_or_paid_or_exactRecursive
        C exponent hexpLt hexp honeLoss htop T
        hUV hUW hVW
      with hdeep | hpair | hpaid | hrec
    · exact Or.inl hdeep
    · exact Or.inr (Or.inl hpair)
    · exact Or.inr (Or.inr (Or.inl hpaid))
    · exact Or.inr (Or.inr (Or.inr (Or.inl hrec)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr hover)))

#print axioms tripleFibre_has_common_word_collision_triangle
#print axioms deficientCore_tripleWord_or_exactTopLossOverload
#print axioms deficientCore_deep_or_highLossPair_or_paid_or_exactRecursive_or_topOverload


/-- Girth-free deficient-core root with recursive data exposed.  The only
structural triangle remainder is a high-layer two-loss pair. -/
theorem deficientCore_deep_or_highLossPair_or_paid_or_exactRecursive_or_topShared
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexpLt : ∀ x, exponent x < n)
    (hexp : ∀ x, exponent x ≤ n)
    (honeLoss :
      ∀ x, (active C x).card ≤ n - exponent x + 1)
    (htop :
      ((Finset.univ : Finset V).filter
        (fun z => exponent z = n - 1)).card ≤ 1)
    {T : Finset V}
    (hdef :
      BlockDeficient
        (fun x => 2 ^ exponent x)
        (enlargedProjectedCandidateBlock C exponent)
        T) :
    (
      ∃ z : V,
        z ∈ projectedLossVertices C exponent ∧
        exponent z + 3 ≤ n
    )
    ∨
    (
      ∃ a b : {x : V // x ∈ T},
        a ≠ b ∧
        a.1 ∈ projectedLossVertices C exponent ∧
        b.1 ∈ projectedLossVertices C exponent ∧
        (
          (exponent a.1 = n - 1 ∧ exponent b.1 = n - 2)
          ∨
          (exponent a.1 = n - 2 ∧ exponent b.1 = n - 1)
          ∨
          (exponent a.1 = n - 2 ∧ exponent b.1 = n - 2)
        )
    )
    ∨
    (
      ∃ z : V,
        1 ≤ dyadicProfileSurplus
          exponent (projectedFree C) z
    )
    ∨
    (
      ∃ source : V,
        ExactRecursiveOutlet C exponent source
    )
    ∨
    (
      ∃ top ∈ T,
        top ∈ projectedLossVertices C exponent ∧
        exponent top = n - 1 ∧
        (
          sharedBlockWords
            (enlargedProjectedCandidateBlock C exponent)
            T top
          ∩
          retainedCompletionWords C top
        ).Nonempty
    ) := by
  rcases
    deficientCore_tripleFibre_or_recursiveOverload
      C exponent hexpLt hexp honeLoss hdef
    with htriple | hexact | htopShared
  · obtain ⟨word,hthree⟩ := htriple
    obtain ⟨u,v,w,_huv,_huw,_hvw,
      _huWord,_hvWord,_hwWord,hUV,hUW,hVW⟩ :=
      tripleFibre_has_common_word_collision_triangle
        C exponent hthree
    rcases
      enlargedCollisionGraph_triangle_deep_or_highPair_or_paid_or_exactRecursive
        C exponent hexpLt hexp honeLoss htop T
        hUV hUW hVW
      with hdeep | hpair | hpaid | hrec
    · exact Or.inl hdeep
    · exact Or.inr (Or.inl hpair)
    · exact Or.inr (Or.inr (Or.inl hpaid))
    · exact Or.inr (Or.inr (Or.inr (Or.inl hrec)))
  · obtain ⟨v,hvT,hvExact,hout⟩ := hexact
    exact Or.inr (Or.inr (Or.inr (Or.inl
      ⟨v,exactSharedOutlet_to_recursive
        C exponent hvExact hout⟩)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr htopShared)))

#print axioms deficientCore_deep_or_highLossPair_or_paid_or_exactRecursive_or_topShared

end OrderedEdgeColoring
end JSP000404Research
