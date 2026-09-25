
import JSP000404Research.ResidualUnsafeEdgeOrder
import JSP000404Research.ResidualOverlapWitness
import Mathlib.Tactic

/-!
# Order budget for unsafe projected overlaps

A retained completion word shared by u<v is compatible with the retained
partial words at both endpoints.

Therefore no retained colour can be simultaneously

  incoming at u and outgoing at v,

because the canonical retained bit would then be true at u and false at v.
In the notation of ResidualUnsafeEdgeBudget, every genuine projected overlap
pair has

  residualThroughColours(u,v) = empty.

If such an overlap pair is also unsafe for residual recolouring, then

  incomingRetained(u) union outgoingRetained(v) = Fin n

and the union is disjoint.  Distinct incoming colours require distinct
vertices strictly to the left of u; distinct outgoing colours require distinct
vertices strictly to the right of v.  Hence an unsafe overlap consumes at
least n exterior vertices.

Combining with the unsafe exponent budget gives the useful order inequality

  exponent(u)+exponent(v)
    <= card(strictLeft(u)) + card(strictRight(v)).

This is a genuine finite-order obstruction: a positive hard overlap cannot
occur close to both ends of the ordered centre set.
-/

namespace JSP000404Research
namespace OrderedEdgeColoring

/-- A common retained completion forbids every through colour. -/
theorem residualThroughColours_eq_empty_of_completion_overlap
    {V : Type*} [LinearOrder V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    {u v : V}
    {word : Fin n → Bool}
    (huWord : word ∈ retainedCompletionWords C u)
    (hvWord : word ∈ retainedCompletionWords C v) :
    residualThroughColours C u v = ∅ := by
  classical
  apply Finset.eq_empty_iff_forall_not_mem.mpr
  intro c hc
  have hcData :=
    (mem_residualThroughColours C u v c).1 hc
  have huComp :=
    (mem_retainedCompletionWords C u word).1 huWord
  have hvComp :=
    (mem_retainedCompletionWords C v word).1 hvWord
  have huBit :
      word c = retainedBit C u c :=
    huComp c
      ((incomingRetained_subset_retainedActive C u) hcData.1)
  have hvBit :
      word c = retainedBit C v c :=
    hvComp c
      ((outgoingRetained_subset_retainedActive C v) hcData.2)
  have hTrue :
      retainedBit C u c = true := by
    exact (mem_incomingRetained_iff_retainedBit_true
      C u c).1 hcData.1
  have hFalse :
      retainedBit C v c = false := by
    unfold retainedBit
    apply bit_eq_false_iff.mpr
    intro hin
    obtain ⟨a, hav, hcol⟩ := hin
    have hout :=
      (mem_outgoingRetained_iff C v c).1 hcData.2
    obtain ⟨w, hvw, hvwCol⟩ := hout
    have hEq : C.color a v = C.color v w := by
      simpa using hcol.trans hvwCol.symm
    exact C.noMonoTwoPath hav hvw hEq
  have hwordTrue : word c = true := huBit.trans hTrue
  have hwordFalse : word c = false := hvBit.trans hFalse
  have htf : true = false := hwordTrue.symm.trans hwordFalse
  cases htf

/-- Incoming retained colours inject into strict-left vertices. -/
theorem incomingRetained_card_le_strictLeft
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (u : V) :
    (incomingRetained C u).card ≤
      (strictLeftVertices u).card := by
  classical
  let chooseLeft :
      {c : Fin n // c ∈ incomingRetained C u} → V :=
    fun c => Classical.choose
      ((mem_incomingRetained_iff C u c.1).1 c.2)
  have hchoose :
      ∀ c : {c : Fin n // c ∈ incomingRetained C u},
        chooseLeft c < u ∧
          C.color (chooseLeft c) u = c.1.castSucc := by
    intro c
    exact Classical.choose_spec
      ((mem_incomingRetained_iff C u c.1).1 c.2)
  have hinj : Function.Injective chooseLeft := by
    intro c d hcd
    apply Subtype.ext
    have hc := (hchoose c).2
    have hd := (hchoose d).2
    rw [hcd] at hc
    have hcast : c.1.castSucc = d.1.castSucc :=
      hc.symm.trans hd
    exact Fin.ext (congrArg Fin.val hcast)
  let f :
      {c : Fin n // c ∈ incomingRetained C u} →
        {a : V // a ∈ strictLeftVertices u} :=
    fun c => ⟨chooseLeft c,
      (mem_strictLeftVertices u (chooseLeft c)).2
        (hchoose c).1⟩
  have hf : Function.Injective f := by
    intro c d h
    apply hinj
    exact congrArg Subtype.val h
  have hcard := Fintype.card_le_of_injective f hf
  simpa [f] using hcard

/-- Outgoing retained colours inject into strict-right vertices. -/
theorem outgoingRetained_card_le_strictRight
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (v : V) :
    (outgoingRetained C v).card ≤
      (strictRightVertices v).card := by
  classical
  let chooseRight :
      {c : Fin n // c ∈ outgoingRetained C v} → V :=
    fun c => Classical.choose
      ((mem_outgoingRetained_iff C v c.1).1 c.2)
  have hchoose :
      ∀ c : {c : Fin n // c ∈ outgoingRetained C v},
        v < chooseRight c ∧
          C.color v (chooseRight c) = c.1.castSucc := by
    intro c
    exact Classical.choose_spec
      ((mem_outgoingRetained_iff C v c.1).1 c.2)
  have hinj : Function.Injective chooseRight := by
    intro c d hcd
    apply Subtype.ext
    have hc := (hchoose c).2
    have hd := (hchoose d).2
    rw [hcd] at hc
    have hcast : c.1.castSucc = d.1.castSucc :=
      hc.symm.trans hd
    exact Fin.ext (congrArg Fin.val hcast)
  let f :
      {c : Fin n // c ∈ outgoingRetained C v} →
        {w : V // w ∈ strictRightVertices v} :=
    fun c => ⟨chooseRight c,
      (mem_strictRightVertices v (chooseRight c)).2
        (hchoose c).1⟩
  have hf : Function.Injective f := by
    intro c d h
    apply hinj
    exact congrArg Subtype.val h
  have hcard := Fintype.card_le_of_injective f hf
  simpa [f] using hcard

/-- Unsafe overlap consumes at least n exterior vertices. -/
theorem unsafe_overlap_n_le_exterior_count
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    {u v : V}
    {word : Fin n → Bool}
    (huWord : word ∈ retainedCompletionWords C u)
    (hvWord : word ∈ retainedCompletionWords C v)
    (hunsafe :
      ¬ ∃ c : Fin n, c ∉ residualForbidden C u v) :
    n ≤ (strictLeftVertices u).card +
      (strictRightVertices v).card := by
  have hthrough :
      residualThroughColours C u v = ∅ :=
    residualThroughColours_eq_empty_of_completion_overlap
      C huWord hvWord
  have hbal := unsafe_residual_card_balance C hunsafe
  rw [hthrough] at hbal
  simp at hbal
  have hleft :=
    incomingRetained_card_le_strictLeft C u
  have hright :=
    outgoingRetained_card_le_strictRight C v
  omega

/-- Sendov-style exponent form for an unsafe residual overlap. -/
theorem unsafe_overlap_exponent_sum_le_exterior_count
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexp : ∀ x, exponent x ≤ n)
    (honeLoss :
      ∀ x, (active C x).card ≤ n - exponent x + 1)
    {u v : V}
    (huv : u < v)
    (hres : IsResidual C u v)
    {word : Fin n → Bool}
    (huWord : word ∈ retainedCompletionWords C u)
    (hvWord : word ∈ retainedCompletionWords C v)
    (hunsafe :
      ¬ ∃ c : Fin n, c ∉ residualForbidden C u v) :
    exponent u + exponent v ≤
      (strictLeftVertices u).card +
        (strictRightVertices v).card := by
  have hthrough :
      residualThroughColours C u v = ∅ :=
    residualThroughColours_eq_empty_of_completion_overlap
      C huWord hvWord
  have hexpBudget :=
    unsafe_residual_exponent_sum_add_through_le
      C exponent hexp honeLoss huv hres hunsafe
  rw [hthrough] at hexpBudget
  simp at hexpBudget
  have hexterior :=
    unsafe_overlap_n_le_exterior_count
      C huWord hvWord hunsafe
  omega

/-- In particular, if the total number of vertices is at most n+1, no
projected overlap edge can be unsafe. -/
theorem overlap_edge_has_safe_colour_of_card_le_n_add_one
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (hcard : Fintype.card V ≤ n + 1)
    {u v : V}
    (huv : u < v)
    {word : Fin n → Bool}
    (huWord : word ∈ retainedCompletionWords C u)
    (hvWord : word ∈ retainedCompletionWords C v) :
    ∃ c : Fin n, c ∉ residualForbidden C u v := by
  by_contra hunsafe
  push_neg at hunsafe
  have hExt :=
    unsafe_overlap_n_le_exterior_count
      C huWord hvWord hunsafe
  have huMem :
      u ∉ strictLeftVertices u := by simp
  have hvMem :
      v ∉ strictRightVertices v := by simp
  have hdisj :
      Disjoint (strictLeftVertices u)
        (strictRightVertices v) := by
    rw [Finset.disjoint_left]
    intro x hxL hxR
    have hxu := (mem_strictLeftVertices u x).1 hxL
    have hvx := (mem_strictRightVertices v x).1 hxR
    linarith
  have hsubset :
      strictLeftVertices u ∪ strictRightVertices v ⊆
        (Finset.univ : Finset V) \ {u,v} := by
    intro x hx
    have hx' := Finset.mem_union.mp hx
    have hxu : x ≠ u := by
      intro hxu
      subst x
      rcases hx' with hxL | hxR
      · exact (lt_irrefl u)
          ((mem_strictLeftVertices u u).1 hxL)
      · exact (not_lt_of_ge huv.le)
          ((mem_strictRightVertices v u).1 hxR)
    have hxv : x ≠ v := by
      intro hxv
      subst x
      rcases hx' with hxL | hxR
      · exact (not_lt_of_ge huv.le)
          ((mem_strictLeftVertices u v).1 hxL)
      · exact (lt_irrefl v)
          ((mem_strictRightVertices v v).1 hxR)
    simp [hxu, hxv]
  have hUnionCard :
      (strictLeftVertices u).card +
          (strictRightVertices v).card
        =
      (strictLeftVertices u ∪
          strictRightVertices v).card := by
    rw [Finset.card_union_of_disjoint hdisj]
  have hcardOutside :
      (strictLeftVertices u).card +
          (strictRightVertices v).card
        ≤ Fintype.card V - 2 := by
    rw [hUnionCard]
    have hle := Finset.card_le_card hsubset
    have huvNe : u ≠ v := ne_of_lt huv
    have hpair : ({u,v} : Finset V).card = 2 :=
      Finset.card_pair huvNe
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ _),
        Finset.card_univ, hpair] at hle
    exact hle
  omega

#print axioms residualThroughColours_eq_empty_of_completion_overlap
#print axioms incomingRetained_card_le_strictLeft
#print axioms outgoingRetained_card_le_strictRight
#print axioms unsafe_overlap_n_le_exterior_count
#print axioms unsafe_overlap_exponent_sum_le_exterior_count
#print axioms overlap_edge_has_safe_colour_of_card_le_n_add_one

end OrderedEdgeColoring
end JSP000404Research
