
import JSP000404Research.ResidualBinaryRecursion
import JSP000404Research.StandardResidual
import JSP000404Research.ResidualActiveDrop
import JSP000404Research.RetainedOrientation
import JSP000404Research.ResidualProjectionLoss
import Mathlib.Tactic

/-!
# Actual n-colour child colourings after splitting the residual high band

Let D have total width n+delta with delta<1 and let C be its standard
(n+1)-band OrderedEdgeColoring.

The two overlapping recursive vertex sets are

  LeftChild  = {v | v is not a high sink},
  RightChild = {v | v is not a high source}.

Every edge internal to LeftChild has direction < n because its upper endpoint
is not a high sink.  Every edge internal to RightChild has direction < n
because its lower endpoint is not a high source.

Hence every internal parent edge is retained, and the parent colouring
restricts canonically to an n-colour OrderedEdgeColoring on each child.

If the parent profile satisfies

  exponent(v) < n
  card(active_C(v)) <= n-exponent(v)+1,

then the transformed child exponents from ResidualBinaryRecursion satisfy

  card(active_child(v)) <= n-childExponent(v).

This is exactly the one-layer local budget for the next integer parameter
n-1, whose standard construction has n colours.
-/

namespace JSP000404Research
namespace DirectionData

open OrderedEdgeColoring

def LeftResidualChild
    {V : Type*} [LinearOrder V] {width : ℝ}
    (D : DirectionData V width) (n : ℕ) :=
  {v : V // ¬ HighSink D n v}

def RightResidualChild
    {V : Type*} [LinearOrder V] {width : ℝ}
    (D : DirectionData V width) (n : ℕ) :=
  {v : V // ¬ HighSource D n v}

theorem width_lt_succ_of_eq_add_delta
    {width delta : ℝ} {n : ℕ}
    (hwidth : width = (n : ℝ) + delta)
    (hdelta : delta < 1) :
    width < (n + 1 : ℕ) := by
  rw [hwidth]
  norm_num
  linarith

theorem leftChild_parentColor_lt
    {V : Type*} [LinearOrder V]
    {width delta : ℝ} {n : ℕ}
    (D : DirectionData V width)
    (hwidth : width = (n : ℝ) + delta)
    (hdelta : delta < 1)
    {u v : LeftResidualChild D n}
    (huv : u < v) :
    ((standardResidualColoring D n
      (width_lt_succ_of_eq_add_delta hwidth hdelta)).color
        u.1 v.1).val < n := by
  have hval :
      D.value u.1 v.1 < (n : ℝ) :=
    value_lt_high_threshold_of_not_sink
      D huv v.2
  by_contra hnot
  have hhigh :
      (n : ℝ) ≤ D.value u.1 v.1 :=
    (standardResidual_iff_high
      D n
      (width_lt_succ_of_eq_add_delta hwidth hdelta)
      huv).1 hnot
  linarith

theorem rightChild_parentColor_lt
    {V : Type*} [LinearOrder V]
    {width delta : ℝ} {n : ℕ}
    (D : DirectionData V width)
    (hwidth : width = (n : ℝ) + delta)
    (hdelta : delta < 1)
    {u v : RightResidualChild D n}
    (huv : u < v) :
    ((standardResidualColoring D n
      (width_lt_succ_of_eq_add_delta hwidth hdelta)).color
        u.1 v.1).val < n := by
  have hval :
      D.value u.1 v.1 < (n : ℝ) :=
    value_lt_high_threshold_of_not_source
      D huv u.2
  by_contra hnot
  have hhigh :
      (n : ℝ) ≤ D.value u.1 v.1 :=
    (standardResidual_iff_high
      D n
      (width_lt_succ_of_eq_add_delta hwidth hdelta)
      huv).1 hnot
  linarith

noncomputable def leftChildColoring
    {V : Type*} [LinearOrder V]
    {width delta : ℝ} {n : ℕ}
    (D : DirectionData V width)
    (hwidth : width = (n : ℝ) + delta)
    (hdelta : delta < 1)
    (hn : 0 < n) :
    OrderedEdgeColoring (LeftResidualChild D n) n := by
  let C :=
    standardResidualColoring D n
      (width_lt_succ_of_eq_add_delta hwidth hdelta)
  refine
    { color := fun u v =>
        if huv : u < v then
          retainedColor C u.1 v.1
            (leftChild_parentColor_lt
              D hwidth hdelta huv)
        else
          ⟨0, hn⟩
      noMonoTwoPath := ?_ }
  intro a v w hav hvw
  simp only [dif_pos hav, dif_pos hvw]
  intro heq
  apply C.noMonoTwoPath hav hvw
  apply Fin.ext
  have hval := congrArg Fin.val heq
  simpa [retainedColor] using hval

noncomputable def rightChildColoring
    {V : Type*} [LinearOrder V]
    {width delta : ℝ} {n : ℕ}
    (D : DirectionData V width)
    (hwidth : width = (n : ℝ) + delta)
    (hdelta : delta < 1)
    (hn : 0 < n) :
    OrderedEdgeColoring (RightResidualChild D n) n := by
  let C :=
    standardResidualColoring D n
      (width_lt_succ_of_eq_add_delta hwidth hdelta)
  refine
    { color := fun u v =>
        if huv : u < v then
          retainedColor C u.1 v.1
            (rightChild_parentColor_lt
              D hwidth hdelta huv)
        else
          ⟨0, hn⟩
      noMonoTwoPath := ?_ }
  intro a v w hav hvw
  simp only [dif_pos hav, dif_pos hvw]
  intro heq
  apply C.noMonoTwoPath hav hvw
  apply Fin.ext
  have hval := congrArg Fin.val heq
  simpa [retainedColor] using hval

@[simp] theorem leftChildColoring_color_of_lt
    {V : Type*} [LinearOrder V]
    {width delta : ℝ} {n : ℕ}
    (D : DirectionData V width)
    (hwidth : width = (n : ℝ) + delta)
    (hdelta : delta < 1)
    (hn : 0 < n)
    {u v : LeftResidualChild D n}
    (huv : u < v) :
    (leftChildColoring D hwidth hdelta hn).color u v =
      retainedColor
        (standardResidualColoring D n
          (width_lt_succ_of_eq_add_delta hwidth hdelta))
        u.1 v.1
        (leftChild_parentColor_lt
          D hwidth hdelta huv) := by
  simp [leftChildColoring, huv]

@[simp] theorem rightChildColoring_color_of_lt
    {V : Type*} [LinearOrder V]
    {width delta : ℝ} {n : ℕ}
    (D : DirectionData V width)
    (hwidth : width = (n : ℝ) + delta)
    (hdelta : delta < 1)
    (hn : 0 < n)
    {u v : RightResidualChild D n}
    (huv : u < v) :
    (rightChildColoring D hwidth hdelta hn).color u v =
      retainedColor
        (standardResidualColoring D n
          (width_lt_succ_of_eq_add_delta hwidth hdelta))
        u.1 v.1
        (rightChild_parentColor_lt
          D hwidth hdelta huv) := by
  simp [rightChildColoring, huv]

theorem leftChild_active_subset_parent_retained
    {V : Type*} [LinearOrder V]
    {width delta : ℝ} {n : ℕ}
    (D : DirectionData V width)
    (hwidth : width = (n : ℝ) + delta)
    (hdelta : delta < 1)
    (hn : 0 < n)
    (v : LeftResidualChild D n) :
    active (leftChildColoring D hwidth hdelta hn) v ⊆
      retainedActive
        (standardResidualColoring D n
          (width_lt_succ_of_eq_add_delta hwidth hdelta))
        v.1 := by
  classical
  let C :=
    standardResidualColoring D n
      (width_lt_succ_of_eq_add_delta hwidth hdelta)
  intro c hc
  simp only [active, Finset.mem_filter, Finset.mem_univ,
    true_and] at hc
  rw [retainedActive_eq_incoming_union_outgoing C v.1]
  rcases hc with ⟨a, hav, hcol⟩ | ⟨w, hvw, hcol⟩
  · apply Finset.mem_union_left
    apply (mem_incomingRetained_iff C v.1 c).2
    refine ⟨a.1, hav, ?_⟩
    apply Fin.ext
    have hval := congrArg Fin.val hcol
    simpa [C, leftChildColoring, hav, retainedColor] using hval.symm
  · apply Finset.mem_union_right
    apply (mem_outgoingRetained_iff C v.1 c).2
    refine ⟨w.1, hvw, ?_⟩
    apply Fin.ext
    have hval := congrArg Fin.val hcol
    simpa [C, leftChildColoring, hvw, retainedColor] using hval.symm

theorem rightChild_active_subset_parent_retained
    {V : Type*} [LinearOrder V]
    {width delta : ℝ} {n : ℕ}
    (D : DirectionData V width)
    (hwidth : width = (n : ℝ) + delta)
    (hdelta : delta < 1)
    (hn : 0 < n)
    (v : RightResidualChild D n) :
    active (rightChildColoring D hwidth hdelta hn) v ⊆
      retainedActive
        (standardResidualColoring D n
          (width_lt_succ_of_eq_add_delta hwidth hdelta))
        v.1 := by
  classical
  let C :=
    standardResidualColoring D n
      (width_lt_succ_of_eq_add_delta hwidth hdelta)
  intro c hc
  simp only [active, Finset.mem_filter, Finset.mem_univ,
    true_and] at hc
  rw [retainedActive_eq_incoming_union_outgoing C v.1]
  rcases hc with ⟨a, hav, hcol⟩ | ⟨w, hvw, hcol⟩
  · apply Finset.mem_union_left
    apply (mem_incomingRetained_iff C v.1 c).2
    refine ⟨a.1, hav, ?_⟩
    apply Fin.ext
    have hval := congrArg Fin.val hcol
    simpa [C, rightChildColoring, hav, retainedColor] using hval.symm
  · apply Finset.mem_union_right
    apply (mem_outgoingRetained_iff C v.1 c).2
    refine ⟨w.1, hvw, ?_⟩
    apply Fin.ext
    have hval := congrArg Fin.val hcol
    simpa [C, rightChildColoring, hvw, retainedColor] using hval.symm

/-- The left child satisfies the next-stage one-layer palette budget. -/
theorem leftChild_active_card_le_next_budget
    {V : Type*} [LinearOrder V]
    {width delta : ℝ} {n : ℕ}
    (D : DirectionData V width)
    (hwidth : width = (n : ℝ) + delta)
    (hdelta : delta < 1)
    (hn : 0 < n)
    (exponent : V → ℕ)
    (hexp : ∀ x, exponent x < n)
    (honeLoss :
      ∀ x,
        (active
          (standardResidualColoring D n
            (width_lt_succ_of_eq_add_delta hwidth hdelta))
          x).card
          ≤ n - exponent x + 1)
    (v : LeftResidualChild D n) :
    (active (leftChildColoring D hwidth hdelta hn) v).card ≤
      n - leftChildExponent D n exponent v.1 := by
  let C :=
    standardResidualColoring D n
      (width_lt_succ_of_eq_add_delta hwidth hdelta)
  have hsub :
      (active (leftChildColoring D hwidth hdelta hn) v).card ≤
        (retainedActive C v.1).card :=
    Finset.card_le_card
      (leftChild_active_subset_parent_retained
        D hwidth hdelta hn v)
  by_cases hsrc : HighSource D n v.1
  · obtain ⟨w, hvw, hhigh⟩ := hsrc
    have hres : IsResidual C v.1 w :=
      (standardResidual_iff_high
        D n
        (width_lt_succ_of_eq_add_delta hwidth hdelta)
        hvw).2 hhigh
    have hresActive :
        residualCoord n ∈ active C v.1 :=
      (residualCoord_mem_active_of_isResidual
        C hvw hres).1
    have hret :
        (retainedActive C v.1).card ≤
          n - exponent v.1 :=
      retainedActive_card_le_of_active_le_add_one_of_residual_mem
        C v.1 (honeLoss v.1) hresActive
    simp [leftChildExponent, hsrc]
    exact hsub.trans hret
  · have hretAct :
        (retainedActive C v.1).card ≤
          (active C v.1).card :=
      retainedActive_card_le_active C v.1
    have hbase :
        (active (leftChildColoring D hwidth hdelta hn) v).card ≤
          n - exponent v.1 + 1 :=
      (hsub.trans hretAct).trans (honeLoss v.1)
    have hcardN :
        (active (leftChildColoring D hwidth hdelta hn) v).card ≤ n := by
      simpa using
        Finset.card_le_univ
          (active (leftChildColoring D hwidth hdelta hn) v)
    simp [leftChildExponent, hsrc]
    have hk := hexp v.1
    omega

/-- Symmetric next-stage budget for the right child. -/
theorem rightChild_active_card_le_next_budget
    {V : Type*} [LinearOrder V]
    {width delta : ℝ} {n : ℕ}
    (D : DirectionData V width)
    (hwidth : width = (n : ℝ) + delta)
    (hdelta : delta < 1)
    (hn : 0 < n)
    (exponent : V → ℕ)
    (hexp : ∀ x, exponent x < n)
    (honeLoss :
      ∀ x,
        (active
          (standardResidualColoring D n
            (width_lt_succ_of_eq_add_delta hwidth hdelta))
          x).card
          ≤ n - exponent x + 1)
    (v : RightResidualChild D n) :
    (active (rightChildColoring D hwidth hdelta hn) v).card ≤
      n - rightChildExponent D n exponent v.1 := by
  let C :=
    standardResidualColoring D n
      (width_lt_succ_of_eq_add_delta hwidth hdelta)
  have hsub :
      (active (rightChildColoring D hwidth hdelta hn) v).card ≤
        (retainedActive C v.1).card :=
    Finset.card_le_card
      (rightChild_active_subset_parent_retained
        D hwidth hdelta hn v)
  by_cases hsink : HighSink D n v.1
  · obtain ⟨u, huv, hhigh⟩ := hsink
    have hres : IsResidual C u v.1 :=
      (standardResidual_iff_high
        D n
        (width_lt_succ_of_eq_add_delta hwidth hdelta)
        huv).2 hhigh
    have hresActive :
        residualCoord n ∈ active C v.1 :=
      (residualCoord_mem_active_of_isResidual
        C huv hres).2
    have hret :
        (retainedActive C v.1).card ≤
          n - exponent v.1 :=
      retainedActive_card_le_of_active_le_add_one_of_residual_mem
        C v.1 (honeLoss v.1) hresActive
    simp [rightChildExponent, hsink]
    exact hsub.trans hret
  · have hretAct :
        (retainedActive C v.1).card ≤
          (active C v.1).card :=
      retainedActive_card_le_active C v.1
    have hbase :
        (active (rightChildColoring D hwidth hdelta hn) v).card ≤
          n - exponent v.1 + 1 :=
      (hsub.trans hretAct).trans (honeLoss v.1)
    have hcardN :
        (active (rightChildColoring D hwidth hdelta hn) v).card ≤ n := by
      simpa using
        Finset.card_le_univ
          (active (rightChildColoring D hwidth hdelta hn) v)
    simp [rightChildExponent, hsink]
    have hk := hexp v.1
    omega

#print axioms leftChildColoring
#print axioms rightChildColoring
#print axioms leftChild_active_subset_parent_retained
#print axioms rightChild_active_subset_parent_retained
#print axioms leftChild_active_card_le_next_budget
#print axioms rightChild_active_card_le_next_budget

end DirectionData
end JSP000404Research
