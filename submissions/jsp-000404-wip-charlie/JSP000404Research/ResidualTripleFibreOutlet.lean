import JSP000404Research.ResidualBoundedMultiplicityAccounting
import JSP000404Research.ResidualEnlargedTriangleOutlet
import JSP000404Research.ResidualLossDirectedFibre
import JSP000404Research.ResidualLossFibreEdgeClassification
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


theorem translated_mem_enlargedProjectedCandidateBlock_of_loss
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    {v : V}
    (hvLoss : v ∈ projectedLossVertices C exponent)
    {word : Fin n → Bool}
    {c : Fin n}
    (hc : c ∈ retainedActive C v)
    (hword : word ∈ translatedCompletionWords C v c) :
    word ∈ enlargedProjectedCandidateBlock C exponent v := by
  rw [enlargedProjectedCandidateBlock_loss C exponent hvLoss]
  unfold allActiveLossCandidateBlock
  apply Finset.mem_union_right
  unfold allActiveTranslatedWords
  exact Finset.mem_biUnion.mpr ⟨c,hc,hword⟩

#print axioms translated_mem_enlargedProjectedCandidateBlock_of_loss

/-- A common word of two distinct loss blocks is localized to the actual
retained edge colour: for an ordered pair x<y it lies in exactly one of the
two edge-colour translated slices.  This is the key semantic refinement of a
high-layer loss-pair witness. -/
theorem lossPair_common_enlarged_word_edgeSlice_xor
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexp : ∀ z, exponent z ≤ n)
    (honeLoss :
      ∀ z, (active C z).card ≤ n - exponent z + 1)
    {x y : V}
    (hxy : x < y)
    (hxLoss : x ∈ projectedLossVertices C exponent)
    (hyLoss : y ∈ projectedLossVertices C exponent)
    {word : Fin n → Bool}
    (hxBlock :
      word ∈ enlargedProjectedCandidateBlock C exponent x)
    (hyBlock :
      word ∈ enlargedProjectedCandidateBlock C exponent y) :
    let hret :=
      projectedLoss_edge_right_retained
        C exponent hexp honeLoss hxLoss hxy
    let e := retainedColor C x y hret
    (
      word ∈ translatedCompletionWords C x e ∧
      word ∉ translatedCompletionWords C y e
    )
    ∨
    (
      word ∈ translatedCompletionWords C y e ∧
      word ∉ translatedCompletionWords C x e
    ) := by
  dsimp
  have hret :=
    projectedLoss_edge_right_retained
      C exponent hexp honeLoss hxLoss hxy
  have hinter :
      word ∈
        allActiveLossCandidateBlock C x ∩
          allActiveLossCandidateBlock C y := by
    apply Finset.mem_inter.mpr
    constructor
    · simpa [enlargedProjectedCandidateBlock_loss
        C exponent hxLoss] using hxBlock
    · simpa [enlargedProjectedCandidateBlock_loss
        C exponent hyLoss] using hyBlock
  exact
    loss_allActive_pair_intersection_edge_slice_xor_of_lt
      C exponent hexp honeLoss
      hxLoss hyLoss hxy hret hinter

/-- Symmetric order-free form of edge-slice localization. -/
theorem lossPair_common_enlarged_word_ordered_edgeSlice_xor
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexp : ∀ z, exponent z ≤ n)
    (honeLoss :
      ∀ z, (active C z).card ≤ n - exponent z + 1)
    {x y : V}
    (hxyNe : x ≠ y)
    (hxLoss : x ∈ projectedLossVertices C exponent)
    (hyLoss : y ∈ projectedLossVertices C exponent)
    {word : Fin n → Bool}
    (hxBlock :
      word ∈ enlargedProjectedCandidateBlock C exponent x)
    (hyBlock :
      word ∈ enlargedProjectedCandidateBlock C exponent y) :
    (
      ∃ hxy : x < y,
        let hret :=
          projectedLoss_edge_right_retained
            C exponent hexp honeLoss hxLoss hxy
        let e := retainedColor C x y hret
        (
          (word ∈ translatedCompletionWords C x e ∧
            word ∉ translatedCompletionWords C y e)
          ∨
          (word ∈ translatedCompletionWords C y e ∧
            word ∉ translatedCompletionWords C x e)
        )
    )
    ∨
    (
      ∃ hyx : y < x,
        let hret :=
          projectedLoss_edge_right_retained
            C exponent hexp honeLoss hyLoss hyx
        let e := retainedColor C y x hret
        (
          (word ∈ translatedCompletionWords C y e ∧
            word ∉ translatedCompletionWords C x e)
          ∨
          (word ∈ translatedCompletionWords C x e ∧
            word ∉ translatedCompletionWords C y e)
        )
    ) := by
  rcases lt_or_gt_of_ne hxyNe with hxy | hyx
  · exact Or.inl
      ⟨hxy,
        lossPair_common_enlarged_word_edgeSlice_xor
          C exponent hexp honeLoss
          hxy hxLoss hyLoss hxBlock hyBlock⟩
  · exact Or.inr
      ⟨hyx,
        lossPair_common_enlarged_word_edgeSlice_xor
          C exponent hexp honeLoss
          hyx hyLoss hxLoss hyBlock hxBlock⟩

#print axioms lossPair_common_enlarged_word_edgeSlice_xor
#print axioms lossPair_common_enlarged_word_ordered_edgeSlice_xor


/-- If a loss block and a non-loss completion block share a word, the loss
side must carry that word in the translated slice indexed by their actual
retained edge colour. -/
theorem loss_nonloss_common_word_edgeSlice_of_lt
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexp : ∀ z, exponent z ≤ n)
    (honeLoss :
      ∀ z, (active C z).card ≤ n - exponent z + 1)
    {x y : V}
    (hxy : x < y)
    (hxLoss : x ∈ projectedLossVertices C exponent)
    (hyNonloss : y ∉ projectedLossVertices C exponent)
    {word : Fin n → Bool}
    (hxBlock :
      word ∈ enlargedProjectedCandidateBlock C exponent x)
    (hyBlock :
      word ∈ enlargedProjectedCandidateBlock C exponent y) :
    let hret :=
      projectedLoss_edge_right_retained
        C exponent hexp honeLoss hxLoss hxy
    word ∈ translatedCompletionWords C x
      (retainedColor C x y hret) := by
  dsimp
  have hyQ :
      word ∈ retainedCompletionWords C y := by
    simpa [enlargedProjectedCandidateBlock_nonloss
      C exponent hyNonloss] using hyBlock
  have hxAll :
      word ∈ allActiveLossCandidateBlock C x := by
    simpa [enlargedProjectedCandidateBlock_loss
      C exponent hxLoss] using hxBlock
  unfold allActiveLossCandidateBlock at hxAll
  rcases Finset.mem_union.mp hxAll with hxQ | hxT
  · exact False.elim
      (Finset.disjoint_left.mp
        (projectedLoss_completion_disjoint
          C exponent hexp honeLoss hxLoss (ne_of_lt hxy))
        hxQ hyQ)
  · obtain ⟨d,hdActive,hdWord⟩ :=
      Finset.mem_biUnion.mp hxT
    have hdInter :
        (translatedCompletionWords C x d ∩
          retainedCompletionWords C y).Nonempty :=
      ⟨word,hdWord,hyQ⟩
    have hedge :=
      loss_translated_intersection_forces_edge_colour
        C exponent hexp honeLoss hxLoss
        (ne_of_lt hxy) hdActive hdInter
    rcases hedge with hforward | hback
    · obtain ⟨_,hretD,hdEq⟩ := hforward
      have hret :=
        projectedLoss_edge_right_retained
          C exponent hexp honeLoss hxLoss hxy
      have hdEdge :
          d = retainedColor C x y hret := by
        apply Fin.ext
        have hval := congrArg Fin.val hdEq
        simpa [retainedColor] using hval
      simpa [hdEdge] using hdWord
    · exact False.elim ((not_lt_of_ge hxy.le) hback.1)

/-- Symmetric incoming version: if x is non-loss, y is loss, and x<y, the
common word lies in y's incoming edge-colour translated slice. -/
theorem nonloss_loss_common_word_edgeSlice_of_lt
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexp : ∀ z, exponent z ≤ n)
    (honeLoss :
      ∀ z, (active C z).card ≤ n - exponent z + 1)
    {x y : V}
    (hxy : x < y)
    (hxNonloss : x ∉ projectedLossVertices C exponent)
    (hyLoss : y ∈ projectedLossVertices C exponent)
    {word : Fin n → Bool}
    (hxBlock :
      word ∈ enlargedProjectedCandidateBlock C exponent x)
    (hyBlock :
      word ∈ enlargedProjectedCandidateBlock C exponent y) :
    let hret :=
      projectedLoss_edge_left_retained
        C exponent hexp honeLoss hyLoss hxy
    word ∈ translatedCompletionWords C y
      (retainedColor C x y hret) := by
  dsimp
  have hxQ :
      word ∈ retainedCompletionWords C x := by
    simpa [enlargedProjectedCandidateBlock_nonloss
      C exponent hxNonloss] using hxBlock
  have hyAll :
      word ∈ allActiveLossCandidateBlock C y := by
    simpa [enlargedProjectedCandidateBlock_loss
      C exponent hyLoss] using hyBlock
  unfold allActiveLossCandidateBlock at hyAll
  rcases Finset.mem_union.mp hyAll with hyQ | hyT
  · have hdisj :=
      projectedLoss_completion_disjoint
        C exponent hexp honeLoss hyLoss (ne_of_gt hxy)
    exact False.elim
      (Finset.disjoint_left.mp hdisj hyQ hxQ)
  · obtain ⟨d,hdActive,hdWord⟩ :=
      Finset.mem_biUnion.mp hyT
    have hdInter :
        (translatedCompletionWords C y d ∩
          retainedCompletionWords C x).Nonempty :=
      ⟨word,hdWord,hxQ⟩
    have hedge :=
      loss_translated_intersection_forces_edge_colour
        C exponent hexp honeLoss hyLoss
        (ne_of_gt hxy) hdActive hdInter
    rcases hedge with hforward | hback
    · exact False.elim ((not_lt_of_ge hxy.le) hforward.1)
    · obtain ⟨_,hretD,hdEq⟩ := hback
      have hret :=
        projectedLoss_edge_left_retained
          C exponent hexp honeLoss hyLoss hxy
      have hdEdge :
          d = retainedColor C x y hret := by
        apply Fin.ext
        have hval := congrArg Fin.val hdEq
        simpa [retainedColor] using hval
      simpa [hdEdge] using hdWord

/-- Ordered exact-two-loss triple carrier, lower two vertices loss and the top
vertex non-loss.  The common word is forced onto the two outgoing triangle
slices, hence is true at both owner coordinates. -/
theorem commonWord_lowerTwoLoss_topNonloss_outgoing_pattern
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexp : ∀ z, exponent z ≤ n)
    (honeLoss :
      ∀ z, (active C z).card ≤ n - exponent z + 1)
    {a b c : V}
    (hab : a < b)
    (hbc : b < c)
    (haLoss : a ∈ projectedLossVertices C exponent)
    (hbLoss : b ∈ projectedLossVertices C exponent)
    (hcNonloss : c ∉ projectedLossVertices C exponent)
    {word : Fin n → Bool}
    (haBlock : word ∈ enlargedProjectedCandidateBlock C exponent a)
    (hbBlock : word ∈ enlargedProjectedCandidateBlock C exponent b)
    (hcBlock : word ∈ enlargedProjectedCandidateBlock C exponent c) :
    let habRet :=
      projectedLoss_edge_right_retained
        C exponent hexp honeLoss haLoss hab
    let hbcRet :=
      projectedLoss_edge_right_retained
        C exponent hexp honeLoss hbLoss hbc
    let eab := retainedColor C a b habRet
    let ebc := retainedColor C b c hbcRet
    word ∈ translatedCompletionWords C a eab ∧
    word ∈ translatedCompletionWords C b ebc ∧
    word eab = true ∧
    word ebc = true := by
  dsimp
  have habRet :=
    projectedLoss_edge_right_retained
      C exponent hexp honeLoss haLoss hab
  have hbcRet :=
    projectedLoss_edge_right_retained
      C exponent hexp honeLoss hbLoss hbc
  let eab := retainedColor C a b habRet
  let ebc := retainedColor C b c hbcRet
  have hbRight :
      word ∈ translatedCompletionWords C b ebc := by
    exact loss_nonloss_common_word_edgeSlice_of_lt
      C exponent hexp honeLoss hbc hbLoss hcNonloss hbBlock hcBlock
  have habXor :=
    lossPair_common_enlarged_word_edgeSlice_xor
      C exponent hexp honeLoss hab haLoss hbLoss haBlock hbBlock
  have heNe : eab ≠ ebc := by
    exact projectedLoss_two_sided_retained_colours_ne
      C exponent hexp honeLoss hbLoss hab hbc
  have heabB :
      eab ∈ retainedActive C b :=
    retainedColor_mem_retainedActive_right C hab habRet
  have hebcB :
      ebc ∈ retainedActive C b :=
    retainedColor_mem_retainedActive_left C hbc hbcRet
  have haLeft :
      word ∈ translatedCompletionWords C a eab := by
    rcases habXor with hA | hB
    · exact hA.1
    · exfalso
      have hdisj :=
        translatedCompletionWords_disjoint_same_owner_distinct_active
          C heabB heNe
      exact Finset.disjoint_left.mp hdisj hB.1 hbRight
  have heabOut :
      eab ∈ outgoingRetained C a := by
    apply (mem_outgoingRetained_iff C a eab).2
    refine ⟨b,hab,?_⟩
    apply Fin.ext
    rfl
  have hebcOut :
      ebc ∈ outgoingRetained C b := by
    apply (mem_outgoingRetained_iff C b ebc).2
    refine ⟨c,hbc,?_⟩
    apply Fin.ext
    rfl
  exact ⟨haLeft,hbRight,
    translated_loss_word_true_of_outgoing C heabOut haLeft,
    translated_loss_word_true_of_outgoing C hebcOut hbRight⟩

/-- Symmetric exact-two-loss pattern: the bottom vertex is non-loss and the
upper two are loss.  The common word lies on the two incoming triangle slices
and is false at both owner coordinates. -/
theorem commonWord_bottomNonloss_upperTwoLoss_incoming_pattern
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexp : ∀ z, exponent z ≤ n)
    (honeLoss :
      ∀ z, (active C z).card ≤ n - exponent z + 1)
    {a b c : V}
    (hab : a < b)
    (hbc : b < c)
    (haNonloss : a ∉ projectedLossVertices C exponent)
    (hbLoss : b ∈ projectedLossVertices C exponent)
    (hcLoss : c ∈ projectedLossVertices C exponent)
    {word : Fin n → Bool}
    (haBlock : word ∈ enlargedProjectedCandidateBlock C exponent a)
    (hbBlock : word ∈ enlargedProjectedCandidateBlock C exponent b)
    (hcBlock : word ∈ enlargedProjectedCandidateBlock C exponent c) :
    let habRet :=
      projectedLoss_edge_left_retained
        C exponent hexp honeLoss hbLoss hab
    let hbcRet :=
      projectedLoss_edge_right_retained
        C exponent hexp honeLoss hbLoss hbc
    let eab := retainedColor C a b habRet
    let ebc := retainedColor C b c hbcRet
    word ∈ translatedCompletionWords C b eab ∧
    word ∈ translatedCompletionWords C c ebc ∧
    word eab = false ∧
    word ebc = false := by
  dsimp
  have habRet :=
    projectedLoss_edge_left_retained
      C exponent hexp honeLoss hbLoss hab
  have hbcRet :=
    projectedLoss_edge_right_retained
      C exponent hexp honeLoss hbLoss hbc
  let eab := retainedColor C a b habRet
  let ebc := retainedColor C b c hbcRet
  have hbLeft :
      word ∈ translatedCompletionWords C b eab :=
    nonloss_loss_common_word_edgeSlice_of_lt
      C exponent hexp honeLoss hab haNonloss hbLoss haBlock hbBlock
  have hbcXor :=
    lossPair_common_enlarged_word_edgeSlice_xor
      C exponent hexp honeLoss hbc hbLoss hcLoss hbBlock hcBlock
  have heNe : eab ≠ ebc := by
    exact projectedLoss_two_sided_retained_colours_ne
      C exponent hexp honeLoss hbLoss hab hbc
  have heabB :
      eab ∈ retainedActive C b :=
    retainedColor_mem_retainedActive_right C hab habRet
  have hebcB :
      ebc ∈ retainedActive C b :=
    retainedColor_mem_retainedActive_left C hbc hbcRet
  have hcRight :
      word ∈ translatedCompletionWords C c ebc := by
    rcases hbcXor with hB | hC
    · exfalso
      have hdisj :=
        translatedCompletionWords_disjoint_same_owner_distinct_active
          C hebcB heNe.symm
      exact Finset.disjoint_left.mp hdisj hB.1 hbLeft
    · exact hC.1
  have heabIn :
      eab ∈ incomingRetained C b := by
    apply (mem_incomingRetained_iff C b eab).2
    refine ⟨a,hab,?_⟩
    apply Fin.ext
    rfl
  have hebcIn :
      ebc ∈ incomingRetained C c := by
    apply (mem_incomingRetained_iff C c ebc).2
    refine ⟨b,hbc,?_⟩
    apply Fin.ext
    rfl
  exact ⟨hbLeft,hcRight,
    translated_loss_word_false_of_incoming C heabIn hbLeft,
    translated_loss_word_false_of_incoming C hebcIn hcRight⟩

#print axioms loss_nonloss_common_word_edgeSlice_of_lt
#print axioms nonloss_loss_common_word_edgeSlice_of_lt
#print axioms commonWord_lowerTwoLoss_topNonloss_outgoing_pattern
#print axioms commonWord_bottomNonloss_upperTwoLoss_incoming_pattern


/-- The remaining exact-two-loss ordering has loss vertices at the two
extremes and a non-loss middle vertex.  The common word is translated
outward from the lower loss and inward to the upper loss, producing a
true/false owner-bit pattern. -/
theorem commonWord_extremeLoss_middleNonloss_cross_pattern
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexp : ∀ z, exponent z ≤ n)
    (honeLoss :
      ∀ z, (active C z).card ≤ n - exponent z + 1)
    {a b c : V}
    (hab : a < b)
    (hbc : b < c)
    (haLoss : a ∈ projectedLossVertices C exponent)
    (hbNonloss : b ∉ projectedLossVertices C exponent)
    (hcLoss : c ∈ projectedLossVertices C exponent)
    {word : Fin n → Bool}
    (haBlock : word ∈ enlargedProjectedCandidateBlock C exponent a)
    (hbBlock : word ∈ enlargedProjectedCandidateBlock C exponent b)
    (hcBlock : word ∈ enlargedProjectedCandidateBlock C exponent c) :
    let habRet :=
      projectedLoss_edge_right_retained
        C exponent hexp honeLoss haLoss hab
    let hbcRet :=
      projectedLoss_edge_left_retained
        C exponent hexp honeLoss hcLoss hbc
    let eab := retainedColor C a b habRet
    let ebc := retainedColor C b c hbcRet
    word ∈ translatedCompletionWords C a eab ∧
    word ∈ translatedCompletionWords C c ebc ∧
    word eab = true ∧
    word ebc = false := by
  dsimp
  have habRet :=
    projectedLoss_edge_right_retained
      C exponent hexp honeLoss haLoss hab
  have hbcRet :=
    projectedLoss_edge_left_retained
      C exponent hexp honeLoss hcLoss hbc
  let eab := retainedColor C a b habRet
  let ebc := retainedColor C b c hbcRet
  have haTrans :
      word ∈ translatedCompletionWords C a eab :=
    loss_nonloss_common_word_edgeSlice_of_lt
      C exponent hexp honeLoss hab haLoss hbNonloss haBlock hbBlock
  have hcTrans :
      word ∈ translatedCompletionWords C c ebc :=
    nonloss_loss_common_word_edgeSlice_of_lt
      C exponent hexp honeLoss hbc hbNonloss hcLoss hbBlock hcBlock
  have heabOut :
      eab ∈ outgoingRetained C a := by
    apply (mem_outgoingRetained_iff C a eab).2
    refine ⟨b,hab,?_⟩
    apply Fin.ext
    rfl
  have hebcIn :
      ebc ∈ incomingRetained C c := by
    apply (mem_incomingRetained_iff C c ebc).2
    refine ⟨b,hbc,?_⟩
    apply Fin.ext
    rfl
  exact ⟨haTrans,hcTrans,
    translated_loss_word_true_of_outgoing C heabOut haTrans,
    translated_loss_word_false_of_incoming C hebcIn hcTrans⟩

#print axioms commonWord_extremeLoss_middleNonloss_cross_pattern


/-- Three translated loss carriers below a top loss cannot all culminate in a
true-labelled top owner coordinate: the two lower owner coordinates and the
top owner's own coordinate give three distinct active coordinates at the top,
contradicting top active-cardinality two. -/
theorem threeTranslatedLoss_topAtUpper_true_impossible
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexp : ∀ q, exponent q ≤ n)
    (honeLoss :
      ∀ q, (active C q).card ≤ n - exponent q + 1)
    {x y z : V}
    (hxy : x < y)
    (hyz : y < z)
    (hxLoss : x ∈ projectedLossVertices C exponent)
    (hyLoss : y ∈ projectedLossVertices C exponent)
    (hzLoss : z ∈ projectedLossVertices C exponent)
    (hzTop : exponent z = n - 1)
    {word : Fin n → Bool}
    {cx cy cz : Fin n}
    (hcx : cx ∈ retainedActive C x)
    (hcy : cy ∈ retainedActive C y)
    (hcz : cz ∈ retainedActive C z)
    (hxT : word ∈ translatedCompletionWords C x cx)
    (hyT : word ∈ translatedCompletionWords C y cy)
    (hzT : word ∈ translatedCompletionWords C z cz)
    (hzTrue : word cz = true) :
    False := by
  have hxz : x < z := lt_trans hxy hyz
  have hyTrue :
      word cy = true := by
    rcases translated_loss_fibre_no_false_before_true
      C exponent hexp honeLoss hyz
      hyLoss hzLoss hcy hcz hyT hzT
      with htrue | hfalse
    · exact htrue
    · rw [hzTrue] at hfalse
      contradiction
  have hxTrue :
      word cx = true := by
    rcases translated_loss_fibre_no_false_before_true
      C exponent hexp honeLoss hxz
      hxLoss hzLoss hcx hcz hxT hzT
      with htrue | hfalse
    · exact htrue
    · rw [hzTrue] at hfalse
      contradiction

  have hxzColour :
      ∃ hret : (C.color x z).val < n,
        retainedColor C x z hret = cx := by
    have hedge :=
      translated_loss_conflict_edge_colour
        C exponent hexp honeLoss
        hxLoss hzLoss (ne_of_lt hxz) hxT hzT
    rcases hedge with hforward | hbackward
    · obtain ⟨_hxz,hret,hcol⟩ := hforward
      rcases hcol with hcxCol | hczCol
      · exact ⟨hret,hcxCol⟩
      · have hzFalse :=
          translated_loss_conflict_upper_colour_forces_word_false
            C exponent hexp honeLoss hxz
            hxLoss hzLoss hcx hcz hxT hzT hret hczCol
        rw [hzTrue] at hzFalse
        contradiction
    · obtain ⟨hzx,_,_⟩ := hbackward
      exact False.elim ((not_lt_of_ge hxz.le) hzx)

  have hyzColour :
      ∃ hret : (C.color y z).val < n,
        retainedColor C y z hret = cy := by
    have hedge :=
      translated_loss_conflict_edge_colour
        C exponent hexp honeLoss
        hyLoss hzLoss (ne_of_lt hyz) hyT hzT
    rcases hedge with hforward | hbackward
    · obtain ⟨_hyz,hret,hcol⟩ := hforward
      rcases hcol with hcyCol | hczCol
      · exact ⟨hret,hcyCol⟩
      · have hzFalse :=
          translated_loss_conflict_upper_colour_forces_word_false
            C exponent hexp honeLoss hyz
            hyLoss hzLoss hcy hcz hyT hzT hret hczCol
        rw [hzTrue] at hzFalse
        contradiction
    · obtain ⟨hzy,_,_⟩ := hbackward
      exact False.elim ((not_lt_of_ge hyz.le) hzy)

  obtain ⟨hxzRet,hxzCol⟩ := hxzColour
  obtain ⟨hyzRet,hyzCol⟩ := hyzColour
  have hcxAtZ : cx ∈ retainedActive C z := by
    rw [retainedActive_eq_incoming_union_outgoing C z]
    apply Finset.mem_union_left
    apply (mem_incomingRetained_iff C z cx).2
    refine ⟨x,hxz,?_⟩
    apply Fin.ext
    have hval := congrArg Fin.val hxzCol
    simpa [retainedColor] using hval
  have hcyAtZ : cy ∈ retainedActive C z := by
    rw [retainedActive_eq_incoming_union_outgoing C z]
    apply Finset.mem_union_left
    apply (mem_incomingRetained_iff C z cy).2
    refine ⟨y,hyz,?_⟩
    apply Fin.ext
    have hval := congrArg Fin.val hyzCol
    simpa [retainedColor] using hval

  have hcxy : cx ≠ cy := by
    intro h
    have hdisj :=
      translated_loss_blocks_disjoint_same_coordinate
        C exponent hexp honeLoss
        hxLoss hyLoss (ne_of_lt hxy) cx
    have hyT' : word ∈ translatedCompletionWords C y cx := by
      simpa [h] using hyT
    exact Finset.disjoint_left.mp hdisj hxT hyT'
  have hcxz : cx ≠ cz := by
    intro h
    have hdisj :=
      translated_loss_blocks_disjoint_same_coordinate
        C exponent hexp honeLoss
        hxLoss hzLoss (ne_of_lt hxz) cx
    have hzT' : word ∈ translatedCompletionWords C z cx := by
      simpa [h] using hzT
    exact Finset.disjoint_left.mp hdisj hxT hzT'
  have hcyz : cy ≠ cz := by
    intro h
    have hdisj :=
      translated_loss_blocks_disjoint_same_coordinate
        C exponent hexp honeLoss
        hyLoss hzLoss (ne_of_lt hyz) cy
    have hzT' : word ∈ translatedCompletionWords C z cy := by
      simpa [h] using hzT
    exact Finset.disjoint_left.mp hdisj hyT hzT'

  have hthree :
      3 ≤ (retainedActive C z).card := by
    have hsub :
        ({cx,cy,cz} : Finset (Fin n)) ⊆ retainedActive C z := by
      intro q hq
      simp only [Finset.mem_insert, Finset.mem_singleton] at hq
      rcases hq with rfl | rfl | rfl
      · exact hcxAtZ
      · exact hcyAtZ
      · exact hcz
    have hcard3 : ({cx,cy,cz} : Finset (Fin n)).card = 3 := by
      simp [hcxy,hcxz,hcyz]
    rw [← hcard3]
    exact Finset.card_le_card hsub
  have htopCard :=
    topLoss_retainedActive_card_eq_two
      C exponent hzLoss hzTop
  omega

/-- Dual extreme-top overflow: if the bottom translated carrier is top-loss
and false-labelled, the two upper owner coordinates plus its own coordinate
give three active coordinates at the bottom, impossible for a top loss. -/
theorem threeTranslatedLoss_topAtLower_false_impossible
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexp : ∀ q, exponent q ≤ n)
    (honeLoss :
      ∀ q, (active C q).card ≤ n - exponent q + 1)
    {x y z : V}
    (hxy : x < y)
    (hyz : y < z)
    (hxLoss : x ∈ projectedLossVertices C exponent)
    (hyLoss : y ∈ projectedLossVertices C exponent)
    (hzLoss : z ∈ projectedLossVertices C exponent)
    (hxTop : exponent x = n - 1)
    {word : Fin n → Bool}
    {cx cy cz : Fin n}
    (hcx : cx ∈ retainedActive C x)
    (hcy : cy ∈ retainedActive C y)
    (hcz : cz ∈ retainedActive C z)
    (hxT : word ∈ translatedCompletionWords C x cx)
    (hyT : word ∈ translatedCompletionWords C y cy)
    (hzT : word ∈ translatedCompletionWords C z cz)
    (hxFalse : word cx = false) :
    False := by
  have hxz : x < z := lt_trans hxy hyz
  have hyFalse :=
    translated_loss_fibre_monotone_bits
      C exponent hexp honeLoss hxy
      hxLoss hyLoss hcx hcy hxT hyT hxFalse
  have hzFalse :=
    translated_loss_fibre_monotone_bits
      C exponent hexp honeLoss hxz
      hxLoss hzLoss hcx hcz hxT hzT hxFalse

  have hxyColour :
      ∃ hret : (C.color x y).val < n,
        retainedColor C x y hret = cy := by
    have hedge :=
      translated_loss_conflict_edge_colour
        C exponent hexp honeLoss
        hxLoss hyLoss (ne_of_lt hxy) hxT hyT
    rcases hedge with hforward | hbackward
    · obtain ⟨_hxy,hret,hcol⟩ := hforward
      rcases hcol with hcxCol | hcyCol
      · have hxTrue :=
          translated_loss_conflict_lower_colour_forces_word_true
            C exponent hexp honeLoss hxy
            hxLoss hyLoss hcx hcy hxT hyT hret hcxCol
        rw [hxFalse] at hxTrue
        contradiction
      · exact ⟨hret,hcyCol⟩
    · obtain ⟨hyx,_,_⟩ := hbackward
      exact False.elim ((not_lt_of_ge hxy.le) hyx)

  have hxzColour :
      ∃ hret : (C.color x z).val < n,
        retainedColor C x z hret = cz := by
    have hedge :=
      translated_loss_conflict_edge_colour
        C exponent hexp honeLoss
        hxLoss hzLoss (ne_of_lt hxz) hxT hzT
    rcases hedge with hforward | hbackward
    · obtain ⟨_hxz,hret,hcol⟩ := hforward
      rcases hcol with hcxCol | hczCol
      · have hxTrue :=
          translated_loss_conflict_lower_colour_forces_word_true
            C exponent hexp honeLoss hxz
            hxLoss hzLoss hcx hcz hxT hzT hret hcxCol
        rw [hxFalse] at hxTrue
        contradiction
      · exact ⟨hret,hczCol⟩
    · obtain ⟨hzx,_,_⟩ := hbackward
      exact False.elim ((not_lt_of_ge hxz.le) hzx)

  obtain ⟨hxyRet,hxyCol⟩ := hxyColour
  obtain ⟨hxzRet,hxzCol⟩ := hxzColour
  have hcyAtX : cy ∈ retainedActive C x := by
    rw [retainedActive_eq_incoming_union_outgoing C x]
    apply Finset.mem_union_right
    apply (mem_outgoingRetained_iff C x cy).2
    refine ⟨y,hxy,?_⟩
    apply Fin.ext
    have hval := congrArg Fin.val hxyCol
    simpa [retainedColor] using hval
  have hczAtX : cz ∈ retainedActive C x := by
    rw [retainedActive_eq_incoming_union_outgoing C x]
    apply Finset.mem_union_right
    apply (mem_outgoingRetained_iff C x cz).2
    refine ⟨z,hxz,?_⟩
    apply Fin.ext
    have hval := congrArg Fin.val hxzCol
    simpa [retainedColor] using hval

  have hcxy : cx ≠ cy := by
    intro h
    have hdisj :=
      translated_loss_blocks_disjoint_same_coordinate
        C exponent hexp honeLoss
        hxLoss hyLoss (ne_of_lt hxy) cx
    have hyT' : word ∈ translatedCompletionWords C y cx := by
      simpa [h] using hyT
    exact Finset.disjoint_left.mp hdisj hxT hyT'
  have hcxz : cx ≠ cz := by
    intro h
    have hdisj :=
      translated_loss_blocks_disjoint_same_coordinate
        C exponent hexp honeLoss
        hxLoss hzLoss (ne_of_lt hxz) cx
    have hzT' : word ∈ translatedCompletionWords C z cx := by
      simpa [h] using hzT
    exact Finset.disjoint_left.mp hdisj hxT hzT'
  have hcyz : cy ≠ cz := by
    intro h
    have hdisj :=
      translated_loss_blocks_disjoint_same_coordinate
        C exponent hexp honeLoss
        hyLoss hzLoss (ne_of_lt hyz) cy
    have hzT' : word ∈ translatedCompletionWords C z cy := by
      simpa [h] using hzT
    exact Finset.disjoint_left.mp hdisj hyT hzT'

  have hthree :
      3 ≤ (retainedActive C x).card := by
    have hsub :
        ({cx,cy,cz} : Finset (Fin n)) ⊆ retainedActive C x := by
      intro q hq
      simp only [Finset.mem_insert, Finset.mem_singleton] at hq
      rcases hq with rfl | rfl | rfl
      · exact hcx
      · exact hcyAtX
      · exact hczAtX
    have hcard3 : ({cx,cy,cz} : Finset (Fin n)).card = 3 := by
      simp [hcxy,hcxz,hcyz]
    rw [← hcard3]
    exact Finset.card_le_card hsub
  have htopCard :=
    topLoss_retainedActive_card_eq_two
      C exponent hxLoss hxTop
  omega

#print axioms threeTranslatedLoss_topAtUpper_true_impossible
#print axioms threeTranslatedLoss_topAtLower_false_impossible


/-- For three translated loss carriers x<y<z with the unique top layer at the
middle vertex y, the top owner coordinate must equal one of the two incident
edge colours (those two colours exhaust the top active palette).  The common
word then falls into exactly one of two mirror patterns:

* the top owner is the left/incoming edge colour; y and z are false-labelled
  on the two incident edge slices;
* the top owner is the right/outgoing edge colour; x and y are true-labelled
  on the two incident edge slices.

This is the finite middle-top state left after extreme-top rank overflow. -/
theorem threeTranslatedLoss_middleTop_two_pattern
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexp : ∀ q, exponent q ≤ n)
    (honeLoss :
      ∀ q, (active C q).card ≤ n - exponent q + 1)
    {x y z : V}
    (hxy : x < y)
    (hyz : y < z)
    (hxLoss : x ∈ projectedLossVertices C exponent)
    (hyLoss : y ∈ projectedLossVertices C exponent)
    (hzLoss : z ∈ projectedLossVertices C exponent)
    (hyTop : exponent y = n - 1)
    {word : Fin n → Bool}
    {cx cy cz : Fin n}
    (hcx : cx ∈ retainedActive C x)
    (hcy : cy ∈ retainedActive C y)
    (hcz : cz ∈ retainedActive C z)
    (hxT : word ∈ translatedCompletionWords C x cx)
    (hyT : word ∈ translatedCompletionWords C y cy)
    (hzT : word ∈ translatedCompletionWords C z cz) :
    let hleft :=
      projectedLoss_edge_left_retained
        C exponent hexp honeLoss hyLoss hxy
    let hright :=
      projectedLoss_edge_right_retained
        C exponent hexp honeLoss hyLoss hyz
    let eleft := retainedColor C x y hleft
    let eright := retainedColor C y z hright
    (
      cy = eleft ∧
      word ∈ translatedCompletionWords C y eleft ∧
      word ∈ translatedCompletionWords C z eright ∧
      word eleft = false ∧
      word eright = false
    )
    ∨
    (
      cy = eright ∧
      word ∈ translatedCompletionWords C x eleft ∧
      word ∈ translatedCompletionWords C y eright ∧
      word eleft = true ∧
      word eright = true
    ) := by
  dsimp
  have hleft :=
    projectedLoss_edge_left_retained
      C exponent hexp honeLoss hyLoss hxy
  have hright :=
    projectedLoss_edge_right_retained
      C exponent hexp honeLoss hyLoss hyz
  let eleft := retainedColor C x y hleft
  let eright := retainedColor C y z hright

  have heleftActive :
      eleft ∈ retainedActive C y :=
    retainedColor_mem_retainedActive_right C hxy hleft
  have herightActive :
      eright ∈ retainedActive C y :=
    retainedColor_mem_retainedActive_left C hyz hright
  have hne :
      eleft ≠ eright :=
    projectedLoss_two_sided_retained_colours_ne
      C exponent hexp honeLoss hyLoss hxy hyz
  have hcard :
      (retainedActive C y).card = 2 :=
    topLoss_retainedActive_card_eq_two
      C exponent hyLoss hyTop
  have hcyCase : cy = eleft ∨ cy = eright := by
    by_contra hnot
    push_neg at hnot
    have hsub :
        ({eleft,eright,cy} : Finset (Fin n)) ⊆ retainedActive C y := by
      intro q hq
      simp only [Finset.mem_insert, Finset.mem_singleton] at hq
      rcases hq with rfl | rfl | rfl
      · exact heleftActive
      · exact herightActive
      · exact hcy
    have hc3 : ({eleft,eright,cy} : Finset (Fin n)).card = 3 := by
      simp [hne,hnot.1,hnot.2]
    have hthree : 3 ≤ (retainedActive C y).card := by
      rw [← hc3]
      exact Finset.card_le_card hsub
    omega

  rcases hcyCase with hcyLeft | hcyRight
  · left
    have hyLeft :
        word ∈ translatedCompletionWords C y eleft := by
      simpa [hcyLeft] using hyT
    have hyzXor :=
      lossPair_common_enlarged_word_edgeSlice_xor
        C exponent hexp honeLoss
        hyz hyLoss hzLoss
        (by simpa [enlargedProjectedCandidateBlock_loss
          C exponent hyLoss, allActiveLossCandidateBlock] using
            (show word ∈ enlargedProjectedCandidateBlock C exponent y from
              by
                rw [enlargedProjectedCandidateBlock_loss C exponent hyLoss]
                unfold allActiveLossCandidateBlock
                apply Finset.mem_union_right
                apply Finset.mem_biUnion.mpr
                exact ⟨cy,hcy,hyT⟩))
        (by
          rw [enlargedProjectedCandidateBlock_loss C exponent hzLoss]
          unfold allActiveLossCandidateBlock
          apply Finset.mem_union_right
          apply Finset.mem_biUnion.mpr
          exact ⟨cz,hcz,hzT⟩)
    have hzRight :
        word ∈ translatedCompletionWords C z eright := by
      rcases hyzXor with hyEdge | hzEdge
      · have hyRight := hyEdge.1
        have hdisj :=
          translatedCompletionWords_disjoint_same_owner_distinct_active
            C heleftActive hne
        exact False.elim
          (Finset.disjoint_left.mp hdisj hyLeft hyRight)
      · exact hzEdge.1
    have heleftIn :
        eleft ∈ incomingRetained C y := by
      apply (mem_incomingRetained_iff C y eleft).2
      refine ⟨x,hxy,?_⟩
      apply Fin.ext
      rfl
    have herightIn :
        eright ∈ incomingRetained C z := by
      apply (mem_incomingRetained_iff C z eright).2
      refine ⟨y,hyz,?_⟩
      apply Fin.ext
      rfl
    exact ⟨hcyLeft,hyLeft,hzRight,
      translated_loss_word_false_of_incoming C heleftIn hyLeft,
      translated_loss_word_false_of_incoming C herightIn hzRight⟩
  · right
    have hyRight :
        word ∈ translatedCompletionWords C y eright := by
      simpa [hcyRight] using hyT
    have hxyXor :=
      lossPair_common_enlarged_word_edgeSlice_xor
        C exponent hexp honeLoss
        hxy hxLoss hyLoss
        (by
          rw [enlargedProjectedCandidateBlock_loss C exponent hxLoss]
          unfold allActiveLossCandidateBlock
          apply Finset.mem_union_right
          apply Finset.mem_biUnion.mpr
          exact ⟨cx,hcx,hxT⟩)
        (by
          rw [enlargedProjectedCandidateBlock_loss C exponent hyLoss]
          unfold allActiveLossCandidateBlock
          apply Finset.mem_union_right
          apply Finset.mem_biUnion.mpr
          exact ⟨cy,hcy,hyT⟩)
    have hxLeft :
        word ∈ translatedCompletionWords C x eleft := by
      rcases hxyXor with hxEdge | hyEdge
      · exact hxEdge.1
      · have hyLeft := hyEdge.1
        have hdisj :=
          translatedCompletionWords_disjoint_same_owner_distinct_active
            C heleftActive hne
        exact False.elim
          (Finset.disjoint_left.mp hdisj hyLeft hyRight)
    have heleftOut :
        eleft ∈ outgoingRetained C x := by
      apply (mem_outgoingRetained_iff C x eleft).2
      refine ⟨y,hxy,?_⟩
      apply Fin.ext
      rfl
    have herightOut :
        eright ∈ outgoingRetained C y := by
      apply (mem_outgoingRetained_iff C y eright).2
      refine ⟨z,hyz,?_⟩
      apply Fin.ext
      rfl
    exact ⟨hcyRight,hxLeft,hyRight,
      translated_loss_word_true_of_outgoing C heleftOut hxLeft,
      translated_loss_word_true_of_outgoing C herightOut hyRight⟩

#print axioms threeTranslatedLoss_middleTop_two_pattern

end OrderedEdgeColoring
end JSP000404Research
