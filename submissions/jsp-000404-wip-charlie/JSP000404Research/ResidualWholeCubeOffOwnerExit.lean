import JSP000404Research.ResidualWholeCubePairExtraSharedWitness
import JSP000404Research.ResidualEnlargedLossCollisionSemantics
import Mathlib.Tactic

/-!
# Off-owner augmenting exit from a whole-cube Q/T pair

A whole-cube pair at active coordinate c consumes exactly the two cubes

  Q_v  and  T_v(c)=Q_s.

Minimality forces an additional shared word outside both cubes.  Since v is a
projected-loss vertex, every word in its enlarged block is either in Q_v or in
an active translated slice T_v(d).  Therefore the extra word lies in some
T_v(d) with d != c.

Combining with the exact whole-cube block intersection shows that this word is
supplied by a third core vertex w distinct from both v and s.

This is the genuine augmenting exit needed by the remaining Q/T/T/T branch.
-/

namespace JSP000404Research
namespace OrderedEdgeColoring

theorem minimal_core_wholeCubeQTPair_has_off_owner_third_exit
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hn3 : 3 ≤ n)
    {T : Finset V}
    (hdef :
      BlockDeficient
        (fun q => 2 ^ exponent q)
        (enlargedProjectedCandidateBlock C exponent)
        T)
    (hmin :
      ∀ U : Finset V,
        U ⊂ T →
        ¬ BlockDeficient
          (fun q => 2 ^ exponent q)
          (enlargedProjectedCandidateBlock C exponent)
          U)
    {s v : V} {c : Fin n}
    (hvT : v ∈ T)
    (hsv : s ≠ v)
    (hsLoss : s ∈ projectedLossVertices C exponent)
    (hvLoss : v ∈ projectedLossVertices C exponent)
    (hvSecond : exponent v = n - 2)
    (hcV : c ∈ retainedActive C v)
    (hwhole : WholeCubeQTPair C s v c) :
    ∃ word : Fin n → Bool,
    ∃ d : Fin n,
    ∃ w : V,
      d ∈ retainedActive C v ∧
      d ≠ c ∧
      word ∈ translatedCompletionWords C v d ∧
      word ∈ enlargedProjectedCandidateBlock C exponent w ∧
      word ∉ retainedCompletionWords C v ∧
      word ∉ retainedCompletionWords C s ∧
      w ∈ T ∧
      w ≠ v ∧
      w ≠ s := by
  obtain ⟨word,w,hvBlock,hwBlock,hnotV,hnotS,hwT,hwNeV,hwNeS⟩ :=
    minimal_core_wholeCubeQTPair_has_third_source
      C exponent hn3 hdef hmin
      hvT hsv hsLoss hvLoss hvSecond hcV hwhole

  have hvLossBlock :
      enlargedProjectedCandidateBlock C exponent v =
        allActiveLossCandidateBlock C v :=
    enlargedProjectedCandidateBlock_loss C exponent hvLoss
  rw [hvLossBlock] at hvBlock
  unfold allActiveLossCandidateBlock at hvBlock
  rcases Finset.mem_union.mp hvBlock with hvQ | hvTrans
  · exact False.elim (hnotV hvQ)
  · unfold allActiveTranslatedWords at hvTrans
    obtain ⟨d,hdActive,hdWord⟩ :=
      Finset.mem_biUnion.mp hvTrans
    have hdc : d ≠ c := by
      intro hdc
      subst d
      rcases hwhole with ⟨_hactiveEq,htransEq⟩
      rw [htransEq] at hdWord
      exact hnotS hdWord
    exact ⟨word,d,w,
      hdActive,hdc,hdWord,hwBlock,
      hnotV,hnotS,hwT,hwNeV,hwNeS⟩

/-- Edge-colour semantics for the off-owner third exit. -/
theorem minimal_core_wholeCubeQTPair_off_owner_exit_edge_semantics
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexp : ∀ q, exponent q ≤ n)
    (honeLoss :
      ∀ q, (active C q).card ≤ n - exponent q + 1)
    (hn3 : 3 ≤ n)
    {T : Finset V}
    (hdef :
      BlockDeficient
        (fun q => 2 ^ exponent q)
        (enlargedProjectedCandidateBlock C exponent)
        T)
    (hmin :
      ∀ U : Finset V,
        U ⊂ T →
        ¬ BlockDeficient
          (fun q => 2 ^ exponent q)
          (enlargedProjectedCandidateBlock C exponent)
          U)
    {s v : V} {c : Fin n}
    (hvT : v ∈ T)
    (hsv : s ≠ v)
    (hsLoss : s ∈ projectedLossVertices C exponent)
    (hvLoss : v ∈ projectedLossVertices C exponent)
    (hvSecond : exponent v = n - 2)
    (hcV : c ∈ retainedActive C v)
    (hwhole : WholeCubeQTPair C s v c) :
    ∃ word : Fin n → Bool,
    ∃ d : Fin n,
    ∃ w : V,
      d ∈ retainedActive C v ∧
      d ≠ c ∧
      word ∈ translatedCompletionWords C v d ∧
      word ∈ enlargedProjectedCandidateBlock C exponent w ∧
      w ∈ T ∧
      w ≠ v ∧
      w ≠ s ∧
      (
        (
          w ∉ projectedLossVertices C exponent ∧
          (
            (∃ hvw : v < w,
              ∃ hret : (C.color v w).val < n,
                retainedColor C v w hret = d)
            ∨
            (∃ hwv : w < v,
              ∃ hret : (C.color w v).val < n,
                retainedColor C w v hret = d)
          )
        )
        ∨
        (
          w ∈ projectedLossVertices C exponent ∧
          (
            (
              word ∈ retainedCompletionWords C w ∧
              (
                (∃ hvw : v < w,
                  ∃ hret : (C.color v w).val < n,
                    retainedColor C v w hret = d)
                ∨
                (∃ hwv : w < v,
                  ∃ hret : (C.color w v).val < n,
                    retainedColor C w v hret = d)
              )
            )
            ∨
            (
              ∃ e : Fin n,
                e ∈ retainedActive C w ∧
                word ∈ translatedCompletionWords C w e ∧
                (
                  (∃ hvw : v < w,
                    ∃ hret : (C.color v w).val < n,
                      retainedColor C v w hret = d ∨
                      retainedColor C v w hret = e)
                  ∨
                  (∃ hwv : w < v,
                    ∃ hret : (C.color w v).val < n,
                      retainedColor C w v hret = d ∨
                      retainedColor C w v hret = e)
                )
            )
          )
        )
      ) := by
  obtain ⟨word,d,w,hdActive,hdc,hdWord,hwBlock,
      _hnotV,_hnotS,hwT,hwNeV,hwNeS⟩ :=
    minimal_core_wholeCubeQTPair_has_off_owner_third_exit
      C exponent hn3 hdef hmin
      hvT hsv hsLoss hvLoss hvSecond hcV hwhole
  have hsem :=
    loss_translated_collision_with_enlarged_block_edge_semantics
      C exponent hexp honeLoss
      hvLoss hwNeV hdActive hdWord hwBlock
  exact ⟨word,d,w,hdActive,hdc,hdWord,hwBlock,
    hwT,hwNeV,hwNeS,hsem⟩

#print axioms minimal_core_wholeCubeQTPair_has_off_owner_third_exit
#print axioms minimal_core_wholeCubeQTPair_off_owner_exit_edge_semantics

end OrderedEdgeColoring
end JSP000404Research
