import JSP000404Research.ResidualProjectedLossCore
import JSP000404Research.ResidualTranslatedFlipExclusion
import JSP000404Research.ResidualBitMerge
import JSP000404Research.ResidualEnlargedCandidateCore
import Mathlib.Tactic

/-!
# Lightweight projected-loss collision semantics

Local Boolean/edge-colour facts needed by whole-cube second-coordinate
recursion.  No Hall, minimal-deficiency, or global capacity machinery is
imported here.
-/

namespace JSP000404Research
namespace OrderedEdgeColoring

theorem projectedLoss_completion_disjoint_core
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexp : ∀ x, exponent x ≤ n)
    (honeLoss :
      ∀ x, (active C x).card ≤ n - exponent x + 1)
    {v w : V}
    (hvLoss : v ∈ projectedLossVertices C exponent)
    (hvw : v ≠ w) :
    Disjoint
      (retainedCompletionWords C v)
      (retainedCompletionWords C w) := by
  classical
  have hvInactive :=
    residual_inactive_of_mem_projectedLossVertices
      C exponent hexp honeLoss hvLoss
  rw [Finset.disjoint_left]
  intro word hvQ hwQ
  rcases lt_or_gt_of_ne hvw with hvwlt | hwvlt
  · have hret : (C.color v w).val < n := by
      by_contra hnot
      have hres : IsResidual C v w := hnot
      exact hvInactive
        (residualCoord_mem_active_of_isResidual C hvwlt hres).1
    let e : Fin n := retainedColor C v w hret
    have heV : e ∈ retainedActive C v :=
      retainedColor_mem_retainedActive_left C hvwlt hret
    have heW : e ∈ retainedActive C w :=
      retainedColor_mem_retainedActive_right C hvwlt hret
    have hvAt :=
      (mem_retainedCompletionWords C v word).1 hvQ e heV
    have hwAt :=
      (mem_retainedCompletionWords C w word).1 hwQ e heW
    have hbits :
        retainedBit C v e = retainedBit C w e :=
      hvAt.symm.trans hwAt
    exact (retainedBit_ne_of_retained_edge C hvwlt hret) hbits
  · have hret : (C.color w v).val < n := by
      by_contra hnot
      have hres : IsResidual C w v := hnot
      exact hvInactive
        (residualCoord_mem_active_of_isResidual C hwvlt hres).2
    let e : Fin n := retainedColor C w v hret
    have heW : e ∈ retainedActive C w :=
      retainedColor_mem_retainedActive_left C hwvlt hret
    have heV : e ∈ retainedActive C v :=
      retainedColor_mem_retainedActive_right C hwvlt hret
    have hwAt :=
      (mem_retainedCompletionWords C w word).1 hwQ e heW
    have hvAt :=
      (mem_retainedCompletionWords C v word).1 hvQ e heV
    have hbits :
        retainedBit C w e = retainedBit C v e :=
      hwAt.symm.trans hvAt
    exact (retainedBit_ne_of_retained_edge C hwvlt hret) hbits

theorem loss_translated_intersection_forces_edge_colour_core
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexp : ∀ x, exponent x ≤ n)
    (honeLoss :
      ∀ x, (active C x).card ≤ n - exponent x + 1)
    {v w : V}
    (hvLoss : v ∈ projectedLossVertices C exponent)
    (hvw : v ≠ w)
    {c : Fin n}
    (hc : c ∈ retainedActive C v)
    (hinter :
      (translatedCompletionWords C v c ∩
        retainedCompletionWords C w).Nonempty) :
    (
      ∃ hvwlt : v < w,
        ∃ hret : (C.color v w).val < n,
          retainedColor C v w hret = c
    )
    ∨
    (
      ∃ hwvlt : w < v,
        ∃ hret : (C.color w v).val < n,
          retainedColor C w v hret = c
    ) := by
  obtain ⟨word,hword⟩ := hinter
  have hvT :
      word ∈ translatedCompletionWords C v c :=
    (Finset.mem_inter.mp hword).1
  have hwQ :
      word ∈ retainedCompletionWords C w :=
    (Finset.mem_inter.mp hword).2
  have hvInactive :=
    residual_inactive_of_mem_projectedLossVertices
      C exponent hexp honeLoss hvLoss
  have hvOrig :
      flipBoolWordAt word c ∈ retainedCompletionWords C v :=
    (mem_translatedCompletionWords C v c word).1 hvT
  rcases lt_or_gt_of_ne hvw with hvwlt | hwvlt
  · left
    have hret : (C.color v w).val < n := by
      by_contra hnot
      have hres : IsResidual C v w := hnot
      exact hvInactive
        (residualCoord_mem_active_of_isResidual C hvwlt hres).1
    refine ⟨hvwlt,hret,?_⟩
    let e : Fin n := retainedColor C v w hret
    by_contra hec
    have heV : e ∈ retainedActive C v :=
      retainedColor_mem_retainedActive_left C hvwlt hret
    have heW : e ∈ retainedActive C w :=
      retainedColor_mem_retainedActive_right C hvwlt hret
    have hvAt :=
      (mem_retainedCompletionWords C v
        (flipBoolWordAt word c)).1 hvOrig e heV
    have hwAt :=
      (mem_retainedCompletionWords C w word).1 hwQ e heW
    have hec' : e ≠ c := by
      intro h
      exact hec (by simpa [e] using h)
    rw [flipBoolWordAt_off word hec'] at hvAt
    have hbits :
        retainedBit C v e = retainedBit C w e :=
      hvAt.symm.trans hwAt
    exact (retainedBit_ne_of_retained_edge C hvwlt hret) hbits
  · right
    have hret : (C.color w v).val < n := by
      by_contra hnot
      have hres : IsResidual C w v := hnot
      exact hvInactive
        (residualCoord_mem_active_of_isResidual C hwvlt hres).2
    refine ⟨hwvlt,hret,?_⟩
    let e : Fin n := retainedColor C w v hret
    by_contra hec
    have heW : e ∈ retainedActive C w :=
      retainedColor_mem_retainedActive_left C hwvlt hret
    have heV : e ∈ retainedActive C v :=
      retainedColor_mem_retainedActive_right C hwvlt hret
    have hvAt :=
      (mem_retainedCompletionWords C v
        (flipBoolWordAt word c)).1 hvOrig e heV
    have hwAt :=
      (mem_retainedCompletionWords C w word).1 hwQ e heW
    have hec' : e ≠ c := by
      intro h
      exact hec (by simpa [e] using h)
    rw [flipBoolWordAt_off word hec'] at hvAt
    have hbits :
        retainedBit C w e = retainedBit C v e :=
      hwAt.symm.trans hvAt
    exact (retainedBit_ne_of_retained_edge C hwvlt hret) hbits

theorem translated_loss_blocks_disjoint_same_coordinate_core
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexp : ∀ x, exponent x ≤ n)
    (honeLoss :
      ∀ x, (active C x).card ≤ n - exponent x + 1)
    {v w : V}
    (hvLoss : v ∈ projectedLossVertices C exponent)
    (hwLoss : w ∈ projectedLossVertices C exponent)
    (hvw : v ≠ w)
    (c : Fin n) :
    Disjoint
      (translatedCompletionWords C v c)
      (translatedCompletionWords C w c) := by
  classical
  rw [Finset.disjoint_left]
  intro word hvT hwT
  have hvQ :
      flipBoolWordAt word c ∈ retainedCompletionWords C v :=
    (mem_translatedCompletionWords C v c word).1 hvT
  have hwQ :
      flipBoolWordAt word c ∈ retainedCompletionWords C w :=
    (mem_translatedCompletionWords C w c word).1 hwT
  exact Finset.disjoint_left.mp
    (projectedLoss_completion_disjoint_core
      C exponent hexp honeLoss hvLoss hvw)
    hvQ hwQ

theorem translated_loss_conflict_edge_colour_core
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexp : ∀ x, exponent x ≤ n)
    (honeLoss :
      ∀ x, (active C x).card ≤ n - exponent x + 1)
    {v w : V}
    (hvLoss : v ∈ projectedLossVertices C exponent)
    (hwLoss : w ∈ projectedLossVertices C exponent)
    (hvw : v ≠ w)
    {c d : Fin n}
    {word : Fin n → Bool}
    (hvT : word ∈ translatedCompletionWords C v c)
    (hwT : word ∈ translatedCompletionWords C w d) :
    (∃ hvwlt : v < w,
      ∃ hret : (C.color v w).val < n,
        retainedColor C v w hret = c ∨
        retainedColor C v w hret = d)
    ∨
    (∃ hwvlt : w < v,
      ∃ hret : (C.color w v).val < n,
        retainedColor C w v hret = c ∨
        retainedColor C w v hret = d) := by
  have hvInactive :=
    residual_inactive_of_mem_projectedLossVertices
      C exponent hexp honeLoss hvLoss
  have hwInactive :=
    residual_inactive_of_mem_projectedLossVertices
      C exponent hexp honeLoss hwLoss
  have hvOrig :
      flipBoolWordAt word c ∈ retainedCompletionWords C v :=
    (mem_translatedCompletionWords C v c word).1 hvT
  have hwOrig :
      flipBoolWordAt word d ∈ retainedCompletionWords C w :=
    (mem_translatedCompletionWords C w d word).1 hwT
  rcases lt_or_gt_of_ne hvw with hvwlt | hwvlt
  · left
    have hret : (C.color v w).val < n := by
      by_contra hnot
      have hres : IsResidual C v w := hnot
      exact hvInactive
        (residualCoord_mem_active_of_isResidual C hvwlt hres).1
    refine ⟨hvwlt,hret,?_⟩
    by_contra hne
    push_neg at hne
    let e : Fin n := retainedColor C v w hret
    have heV : e ∈ retainedActive C v :=
      retainedColor_mem_retainedActive_left C hvwlt hret
    have heW : e ∈ retainedActive C w :=
      retainedColor_mem_retainedActive_right C hvwlt hret
    have hvAt :=
      (mem_retainedCompletionWords C v
        (flipBoolWordAt word c)).1 hvOrig e heV
    have hwAt :=
      (mem_retainedCompletionWords C w
        (flipBoolWordAt word d)).1 hwOrig e heW
    have hec : e ≠ c := by simpa [e] using hne.1
    have hed : e ≠ d := by simpa [e] using hne.2
    rw [flipBoolWordAt_off word hec] at hvAt
    rw [flipBoolWordAt_off word hed] at hwAt
    exact (retainedBit_ne_of_retained_edge C hvwlt hret)
      (hvAt.symm.trans hwAt)
  · right
    have hret : (C.color w v).val < n := by
      by_contra hnot
      have hres : IsResidual C w v := hnot
      exact hwInactive
        (residualCoord_mem_active_of_isResidual C hwvlt hres).1
    refine ⟨hwvlt,hret,?_⟩
    by_contra hne
    push_neg at hne
    let e : Fin n := retainedColor C w v hret
    have heW : e ∈ retainedActive C w :=
      retainedColor_mem_retainedActive_left C hwvlt hret
    have heV : e ∈ retainedActive C v :=
      retainedColor_mem_retainedActive_right C hwvlt hret
    have hvAt :=
      (mem_retainedCompletionWords C v
        (flipBoolWordAt word c)).1 hvOrig e heV
    have hwAt :=
      (mem_retainedCompletionWords C w
        (flipBoolWordAt word d)).1 hwOrig e heW
    have hec : e ≠ c := by simpa [e] using hne.1
    have hed : e ≠ d := by simpa [e] using hne.2
    rw [flipBoolWordAt_off word hec] at hvAt
    rw [flipBoolWordAt_off word hed] at hwAt
    exact (retainedBit_ne_of_retained_edge C hwvlt hret)
      (hwAt.symm.trans hvAt)

theorem translated_loss_conflict_distinct_coordinates_core
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexp : ∀ x, exponent x ≤ n)
    (honeLoss :
      ∀ x, (active C x).card ≤ n - exponent x + 1)
    {v w : V}
    (hvLoss : v ∈ projectedLossVertices C exponent)
    (hwLoss : w ∈ projectedLossVertices C exponent)
    (hvw : v ≠ w)
    {c d : Fin n}
    (hoverlap :
      (translatedCompletionWords C v c ∩
        translatedCompletionWords C w d).Nonempty) :
    c ≠ d := by
  intro hcd
  subst d
  obtain ⟨word,hword⟩ := hoverlap
  have hvT :
      word ∈ translatedCompletionWords C v c :=
    (Finset.mem_inter.mp hword).1
  have hwT :
      word ∈ translatedCompletionWords C w c :=
    (Finset.mem_inter.mp hword).2
  exact Finset.disjoint_left.mp
    (translated_loss_blocks_disjoint_same_coordinate_core
      C exponent hexp honeLoss hvLoss hwLoss hvw c)
    hvT hwT

theorem loss_translated_collision_with_enlarged_block_edge_semantics_core
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
      exact loss_translated_intersection_forces_edge_colour_core
        C exponent hexp honeLoss hvLoss hvw hc
        ⟨word,Finset.mem_inter.mpr ⟨hvT,hwQ⟩⟩
    · right
      unfold allActiveTranslatedWords at hwT
      obtain ⟨d,hdActive,hdWord⟩ :=
        Finset.mem_biUnion.mp hwT
      refine ⟨d,hdActive,hdWord,?_⟩
      exact translated_loss_conflict_edge_colour_core
        C exponent hexp honeLoss
        hvLoss hwLoss hvw hvT hdWord
  · left
    refine ⟨hwLoss,?_⟩
    rw [enlargedProjectedCandidateBlock_nonloss
      C exponent hwLoss] at hwBlock
    exact loss_translated_intersection_forces_edge_colour_core
      C exponent hexp honeLoss hvLoss hvw hc
      ⟨word,Finset.mem_inter.mpr ⟨hvT,hwBlock⟩⟩

#print axioms projectedLoss_completion_disjoint_core
#print axioms loss_translated_intersection_forces_edge_colour_core
#print axioms translated_loss_conflict_edge_colour_core
#print axioms translated_loss_conflict_distinct_coordinates_core
#print axioms loss_translated_collision_with_enlarged_block_edge_semantics_core

end OrderedEdgeColoring
end JSP000404Research
