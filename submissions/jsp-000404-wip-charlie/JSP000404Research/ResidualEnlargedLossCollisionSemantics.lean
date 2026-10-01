import JSP000404Research.ResidualEnlargedLossTranslatedCollision
import JSP000404Research.ResidualLossTranslatedConflict
import JSP000404Research.ResidualLossAllActiveBlockerUnique
import Mathlib.Tactic

/-!
# Edge semantics of translated collisions in an enlarged minimal core

Every projected-loss vertex in a minimal deficient enlarged candidate core
exposes a translated collision

  word in T_{v,c} ∩ B_w

with another core vertex w.

This file records the exact retained-edge semantics.

* If w is non-loss, B_w = Q_w and the actual retained edge colour vw is c.
* If w is loss and the shared word lies in Q_w, again the edge colour is c.
* If w is loss and the shared word lies in an active translated slice T_{w,d},
  the edge colour is c or d.

Thus every translated collision edge is owned by one of the translated
coordinates exposed at its endpoints.
-/

namespace JSP000404Research
namespace OrderedEdgeColoring

theorem loss_translated_collision_with_enlarged_block_edge_semantics
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexp : ∀ x, exponent x ≤ n)
    (honeLoss :
      ∀ x, (active C x).card ≤ n - exponent x + 1)
    {v w : V}
    (hvLoss : v ∈ projectedLossVertices C exponent)
    (hvw : v ≠ w)
    {word : Fin n → Bool}
    {c : Fin n}
    (hc : c ∈ retainedActive C v)
    (hvT : word ∈ translatedCompletionWords C v c)
    (hwBlock :
      word ∈ enlargedProjectedCandidateBlock C exponent w) :
    (
      w ∉ projectedLossVertices C exponent ∧
      (
        (∃ hvwlt : v < w,
          ∃ hret : (C.color v w).val < n,
            retainedColor C v w hret = c)
        ∨
        (∃ hwvlt : w < v,
          ∃ hret : (C.color w v).val < n,
            retainedColor C w v hret = c)
      )
    )
    ∨
    (
      w ∈ projectedLossVertices C exponent ∧
      (
        (
          word ∈ retainedCompletionWords C w ∧
          (
            (∃ hvwlt : v < w,
              ∃ hret : (C.color v w).val < n,
                retainedColor C v w hret = c)
            ∨
            (∃ hwvlt : w < v,
              ∃ hret : (C.color w v).val < n,
                retainedColor C w v hret = c)
          )
        )
        ∨
        (
          ∃ d : Fin n,
            d ∈ retainedActive C w ∧
            word ∈ translatedCompletionWords C w d ∧
            (
              (∃ hvwlt : v < w,
                ∃ hret : (C.color v w).val < n,
                  retainedColor C v w hret = c ∨
                  retainedColor C v w hret = d)
              ∨
              (∃ hwvlt : w < v,
                ∃ hret : (C.color w v).val < n,
                  retainedColor C w v hret = c ∨
                  retainedColor C w v hret = d)
            )
        )
      )
    ) := by
  classical
  by_cases hwLoss : w ∈ projectedLossVertices C exponent
  · right
    refine ⟨hwLoss,?_⟩
    rw [enlargedProjectedCandidateBlock_loss
      C exponent hwLoss] at hwBlock
    unfold allActiveLossCandidateBlock at hwBlock
    rcases Finset.mem_union.mp hwBlock with hwQ | hwT
    · left
      refine ⟨hwQ,?_⟩
      have hinter :
          (translatedCompletionWords C v c ∩
            retainedCompletionWords C w).Nonempty := by
        exact ⟨word,Finset.mem_inter.mpr ⟨hvT,hwQ⟩⟩
      exact loss_translated_intersection_forces_edge_colour
        C exponent hexp honeLoss
        hvLoss hvw hc hinter
    · right
      unfold allActiveTranslatedWords at hwT
      obtain ⟨d,hdActive,hdWord⟩ :=
        Finset.mem_biUnion.mp hwT
      refine ⟨d,hdActive,hdWord,?_⟩
      exact translated_loss_conflict_edge_colour
        C exponent hexp honeLoss
        hvLoss hwLoss hvw hvT hdWord
  · left
    refine ⟨hwLoss,?_⟩
    rw [enlargedProjectedCandidateBlock_nonloss
      C exponent hwLoss] at hwBlock
    have hinter :
        (translatedCompletionWords C v c ∩
          retainedCompletionWords C w).Nonempty := by
      exact ⟨word,Finset.mem_inter.mpr ⟨hvT,hwBlock⟩⟩
    exact loss_translated_intersection_forces_edge_colour
      C exponent hexp honeLoss
      hvLoss hvw hc hinter

theorem minimal_enlargedCandidate_loss_has_owned_collision_edge
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexp : ∀ x, exponent x ≤ n)
    (honeLoss :
      ∀ x, (active C x).card ≤ n - exponent x + 1)
    {T : Finset V}
    (hdef :
      BlockDeficient
        (fun x => 2 ^ exponent x)
        (enlargedProjectedCandidateBlock C exponent)
        T)
    (hmin :
      ∀ U : Finset V,
        U ⊂ T →
        ¬ BlockDeficient
          (fun x => 2 ^ exponent x)
          (enlargedProjectedCandidateBlock C exponent)
          U)
    {v : V}
    (hvTmem : v ∈ T)
    (hvLoss : v ∈ projectedLossVertices C exponent)
    (hvLt : exponent v < n) :
    ∃ w : V,
      w ∈ T ∧
      w ≠ v ∧
      ∃ word : Fin n → Bool,
      ∃ c : Fin n,
        c ∈ retainedActive C v ∧
        word ∈ translatedCompletionWords C v c ∧
        word ∈ enlargedProjectedCandidateBlock C exponent w ∧
        (
          (∃ hvwlt : v < w,
            ∃ hret : (C.color v w).val < n,
              retainedColor C v w hret = c ∨
              ∃ d : Fin n,
                d ∈ retainedActive C w ∧
                retainedColor C v w hret = d)
          ∨
          (∃ hwvlt : w < v,
            ∃ hret : (C.color w v).val < n,
              retainedColor C w v hret = c ∨
              ∃ d : Fin n,
                d ∈ retainedActive C w ∧
                retainedColor C w v hret = d)
        ) := by
  obtain ⟨word,c,hc,hvWord,w,hwT,hwv,hwWord⟩ :=
    minimal_enlargedCandidate_loss_has_translated_collision
      C exponent hdef hmin hvTmem hvLoss hvLt
  have hsem :=
    loss_translated_collision_with_enlarged_block_edge_semantics
      C exponent hexp honeLoss
      hvLoss hwv hc hvWord hwWord
  refine ⟨w,hwT,hwv,word,c,hc,hvWord,hwWord,?_⟩
  rcases hsem with hnon | hloss
  · rcases hnon.2 with hright | hleft
    · left
      obtain ⟨hvw,hret,hcol⟩ := hright
      exact ⟨hvw,hret,Or.inl hcol⟩
    · right
      obtain ⟨hwvlt,hret,hcol⟩ := hleft
      exact ⟨hwvlt,hret,Or.inl hcol⟩
  · rcases hloss.2 with hQ | hT
    · rcases hQ.2 with hright | hleft
      · left
        obtain ⟨hvw,hret,hcol⟩ := hright
        exact ⟨hvw,hret,Or.inl hcol⟩
      · right
        obtain ⟨hwvlt,hret,hcol⟩ := hleft
        exact ⟨hwvlt,hret,Or.inl hcol⟩
    · obtain ⟨d,hd,hdWord,hedge⟩ := hT
      rcases hedge with hright | hleft
      · left
        obtain ⟨hvw,hret,hcol⟩ := hright
        rcases hcol with hcEq | hdEq
        · exact ⟨hvw,hret,Or.inl hcEq⟩
        · exact ⟨hvw,hret,Or.inr ⟨d,hd,hdEq⟩⟩
      · right
        obtain ⟨hwvlt,hret,hcol⟩ := hleft
        rcases hcol with hcEq | hdEq
        · exact ⟨hwvlt,hret,Or.inl hcEq⟩
        · exact ⟨hwvlt,hret,Or.inr ⟨d,hd,hdEq⟩⟩

#print axioms minimal_enlargedCandidate_loss_has_owned_collision_edge

end OrderedEdgeColoring
end JSP000404Research
