
import JSP000404Research.StandardResidualNestedRepair
import JSP000404Research.ResidualUnsafeEdgeBudget
import Mathlib.Tactic

/-!
# Crossing unsafe-overlap carriers: safe cross or strict Boolean growth

Let

  u < a < v < b

and suppose u--v and a--b are unsafe projected-overlap residual carriers.

The standard residual interval theorem forces the crossing edge a--v to be
residual.

There are then two possibilities.

* a--v has a safe retained target colour; this is an augmenting edge.

* a--v is itself unsafe.  Since u--v is unsafe-overlap,
  outgoing(v) is the complement of incoming(u).  Unsafety of a--v gives

      incoming(a) union outgoing(v) = Fin n,

  hence incoming(u) subset incoming(a).

  Equality is impossible: the two original unsafe-overlap words would then be
  the same characteristic word and would lie in the three completion cubes
  Q_u,Q_a,Q_v, contradicting multiplicity at most two.

  Therefore

      incoming(u) proper-subset incoming(a).

  Every new colour in incoming(a)\incoming(u) belongs to outgoing(v), so it
  is a through colour of the crossing residual edge a--v.  In particular its
  through-colour set is nonempty.

Under the one-layer exponent budget this yields the strict credit

  exponent(a) + exponent(v) + 1 <= n.

Thus unresolved crossing hard carriers generate strict Boolean-lattice growth
and a quantitative exponent saving.
-/

namespace JSP000404Research
namespace DirectionData

open OrderedEdgeColoring

/-- A crossing pair of residual carriers forces the middle source-to-sink
cross edge a--v to be residual. -/
theorem standardResidual_crossing_middle_edge
    {V : Type*} [LinearOrder V]
    {t : ℝ} {n : ℕ}
    (D : DirectionData V t)
    (hwidth : t < (n + 1 : ℕ))
    {u a v b : V}
    (hua : u < a)
    (hav : a < v)
    (hvb : v < b)
    (hresUV :
      IsResidual (standardResidualColoring D n hwidth) u v)
    (hresAB :
      IsResidual (standardResidualColoring D n hwidth) a b) :
    IsResidual (standardResidualColoring D n hwidth) a v := by
  let R := standardResidualColoring D n hwidth
  have haTrue :
      residualBit R a = true :=
    residualBit_eq_true_of_residual
      R (hav.trans hvb) hresAB
  exact
    (standardResidual_right_child_iff_bit_true
      D hwidth hua hav hresUV).2 haTrue

/-- If the crossing middle edge is unsafe, lower incoming sets are nested. -/
theorem crossing_middle_unsafe_incoming_subset
    {V : Type*} [LinearOrder V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    {u a v : V}
    {wordUV : Fin n → Bool}
    (hunsafeUV :
      ¬ ∃ c : Fin n, c ∉ residualForbidden C u v)
    (huWord :
      wordUV ∈ retainedCompletionWords C u)
    (hvWord :
      wordUV ∈ retainedCompletionWords C v)
    (hunsafeAV :
      ¬ ∃ c : Fin n, c ∉ residualForbidden C a v) :
    incomingRetained C u ⊆ incomingRetained C a := by
  have hdisj :
      Disjoint (incomingRetained C u) (outgoingRetained C v) :=
    incoming_disjoint_outgoing_of_unsafe_overlap
      C huWord hvWord
  have hunion :=
    unsafe_residual_union_eq_univ C hunsafeAV
  intro c hcu
  have hnotOv : c ∉ outgoingRetained C v := by
    intro hcv
    exact Finset.disjoint_left.mp hdisj hcu hcv
  have hc :
      c ∈ incomingRetained C a ∪ outgoingRetained C v := by
    rw [hunion]
    simp
  rw [Finset.mem_union] at hc
  rcases hc with hca | hcv
  · exact hca
  · exact False.elim (hnotOv hcv)

/-- In the genuine crossing-hard situation that inclusion is strict. -/
theorem crossing_middle_unsafe_incoming_ne
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    {u a v b : V}
    (hua : u < a)
    (hav : a < v)
    (hvb : v < b)
    {wordUV wordAB : Fin n → Bool}
    (hunsafeUV :
      ¬ ∃ c : Fin n, c ∉ residualForbidden C u v)
    (hunsafeAB :
      ¬ ∃ c : Fin n, c ∉ residualForbidden C a b)
    (huWord :
      wordUV ∈ retainedCompletionWords C u)
    (hvWord :
      wordUV ∈ retainedCompletionWords C v)
    (haWord :
      wordAB ∈ retainedCompletionWords C a)
    (hbWord :
      wordAB ∈ retainedCompletionWords C b)
    (hunsafeAV :
      ¬ ∃ c : Fin n, c ∉ residualForbidden C a v) :
    incomingRetained C u ≠ incomingRetained C a := by
  intro hEq
  have hcharEq :
      incomingCharacteristic C u =
        incomingCharacteristic C a := by
    funext c
    simp [incomingCharacteristic, hEq]
  have hwordUV :=
    unsafe_overlap_word_eq_incomingCharacteristic
      C hunsafeUV huWord hvWord
  have hwordAB :=
    unsafe_overlap_word_eq_incomingCharacteristic
      C hunsafeAB haWord hbWord
  have hwords :
      wordUV = wordAB := by
    rw [hwordUV, hwordAB, hcharEq]
  subst wordAB
  exact no_three_distinct_share_retained_completion
    C (ne_of_lt hua)
      (ne_of_lt (hua.trans hav))
      (ne_of_lt hav)
      huWord haWord hvWord

/-- If the middle crossing edge is unsafe, it has a through colour. -/
theorem crossing_middle_unsafe_has_through_colour
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    {u a v b : V}
    (hua : u < a)
    (hav : a < v)
    (hvb : v < b)
    {wordUV wordAB : Fin n → Bool}
    (hunsafeUV :
      ¬ ∃ c : Fin n, c ∉ residualForbidden C u v)
    (hunsafeAB :
      ¬ ∃ c : Fin n, c ∉ residualForbidden C a b)
    (huWord :
      wordUV ∈ retainedCompletionWords C u)
    (hvWord :
      wordUV ∈ retainedCompletionWords C v)
    (haWord :
      wordAB ∈ retainedCompletionWords C a)
    (hbWord :
      wordAB ∈ retainedCompletionWords C b)
    (hunsafeAV :
      ¬ ∃ c : Fin n, c ∉ residualForbidden C a v) :
    (residualThroughColours C a v).Nonempty := by
  classical
  have hsub :
      incomingRetained C u ⊆ incomingRetained C a :=
    crossing_middle_unsafe_incoming_subset
      C hunsafeUV huWord hvWord hunsafeAV
  have hne :
      incomingRetained C u ≠ incomingRetained C a :=
    crossing_middle_unsafe_incoming_ne
      C hua hav hvb hunsafeUV hunsafeAB
      huWord hvWord haWord hbWord hunsafeAV
  have hex :
      ∃ c,
        c ∈ incomingRetained C a ∧
        c ∉ incomingRetained C u := by
    by_contra hno
    push_neg at hno
    have hrev :
        incomingRetained C a ⊆ incomingRetained C u := by
      intro c hc
      exact hno c hc
    exact hne (Finset.Subset.antisymm hsub hrev)
  obtain ⟨c, hca, hnotU⟩ := hex
  have hunionUV :=
    unsafe_residual_union_eq_univ C hunsafeUV
  have hcv :
      c ∈ outgoingRetained C v := by
    have hc :
        c ∈ incomingRetained C u ∪ outgoingRetained C v := by
      rw [hunionUV]
      simp
    rw [Finset.mem_union] at hc
    rcases hc with hcu | hcv
    · exact False.elim (hnotU hcu)
    · exact hcv
  exact ⟨c,
    (mem_residualThroughColours C a v c).2
      ⟨hca, hcv⟩⟩

/-- Crossing repair dichotomy: safe middle cross edge, or nonempty through
credit. -/
theorem crossing_unsafe_overlap_safe_or_through
    {V : Type*} [LinearOrder V] [Fintype V]
    {t : ℝ} {n : ℕ}
    (D : DirectionData V t)
    (hwidth : t < (n + 1 : ℕ))
    {u a v b : V}
    (hua : u < a)
    (hav : a < v)
    (hvb : v < b)
    {wordUV wordAB : Fin n → Bool}
    (hunsafeUV :
      ¬ ∃ c : Fin n,
        c ∉ residualForbidden
          (standardResidualColoring D n hwidth) u v)
    (hunsafeAB :
      ¬ ∃ c : Fin n,
        c ∉ residualForbidden
          (standardResidualColoring D n hwidth) a b)
    (huWord :
      wordUV ∈ retainedCompletionWords
        (standardResidualColoring D n hwidth) u)
    (hvWord :
      wordUV ∈ retainedCompletionWords
        (standardResidualColoring D n hwidth) v)
    (haWord :
      wordAB ∈ retainedCompletionWords
        (standardResidualColoring D n hwidth) a)
    (hbWord :
      wordAB ∈ retainedCompletionWords
        (standardResidualColoring D n hwidth) b) :
    (∃ c : Fin n,
      c ∉ residualForbidden
        (standardResidualColoring D n hwidth) a v)
    ∨
    (residualThroughColours
      (standardResidualColoring D n hwidth) a v).Nonempty := by
  by_cases hsafe :
      ∃ c : Fin n,
        c ∉ residualForbidden
          (standardResidualColoring D n hwidth) a v
  · exact Or.inl hsafe
  · right
    exact crossing_middle_unsafe_has_through_colour
      (standardResidualColoring D n hwidth)
      hua hav hvb
      hunsafeUV hunsafeAB
      huWord hvWord haWord hbWord hsafe

/-- Quantitative form: if the forced crossing edge remains unsafe, it gains
one full through-colour unit in the exponent budget. -/
theorem crossing_unsafe_overlap_cross_exponent_credit
    {V : Type*} [LinearOrder V] [Fintype V]
    {t : ℝ} {n : ℕ}
    (D : DirectionData V t)
    (hwidth : t < (n + 1 : ℕ))
    (exponent : V → ℕ)
    (hexp : ∀ x, exponent x ≤ n)
    (honeLoss :
      ∀ x,
        (active (standardResidualColoring D n hwidth) x).card
          ≤ n - exponent x + 1)
    {u a v b : V}
    (hua : u < a)
    (hav : a < v)
    (hvb : v < b)
    {wordUV wordAB : Fin n → Bool}
    (hunsafeUV :
      ¬ ∃ c : Fin n,
        c ∉ residualForbidden
          (standardResidualColoring D n hwidth) u v)
    (hunsafeAB :
      ¬ ∃ c : Fin n,
        c ∉ residualForbidden
          (standardResidualColoring D n hwidth) a b)
    (huWord :
      wordUV ∈ retainedCompletionWords
        (standardResidualColoring D n hwidth) u)
    (hvWord :
      wordUV ∈ retainedCompletionWords
        (standardResidualColoring D n hwidth) v)
    (haWord :
      wordAB ∈ retainedCompletionWords
        (standardResidualColoring D n hwidth) a)
    (hbWord :
      wordAB ∈ retainedCompletionWords
        (standardResidualColoring D n hwidth) b)
    (hunsafeAV :
      ¬ ∃ c : Fin n,
        c ∉ residualForbidden
          (standardResidualColoring D n hwidth) a v) :
    exponent a + exponent v + 1 ≤ n := by
  let R := standardResidualColoring D n hwidth
  have hresUV :
      IsResidual R u v :=
    isResidual_of_retainedCompletion_overlap_lt
      R (hua.trans hav) huWord hvWord
  have hresAB :
      IsResidual R a b :=
    isResidual_of_retainedCompletion_overlap_lt
      R (hav.trans hvb) haWord hbWord
  have hresAV :
      IsResidual R a v :=
    standardResidual_crossing_middle_edge
      D hwidth hua hav hvb hresUV hresAB
  have hthrough :
      (residualThroughColours R a v).Nonempty :=
    crossing_middle_unsafe_has_through_colour
      R hua hav hvb
      hunsafeUV hunsafeAB
      huWord hvWord haWord hbWord hunsafeAV
  have hcardPos :
      1 ≤ (residualThroughColours R a v).card :=
    Finset.one_le_card.mpr hthrough
  have hbudget :=
    unsafe_residual_exponent_sum_add_through_le
      R exponent hexp honeLoss hav hresAV hunsafeAV
  omega

#print axioms standardResidual_crossing_middle_edge
#print axioms crossing_middle_unsafe_incoming_subset
#print axioms crossing_middle_unsafe_has_through_colour
#print axioms crossing_unsafe_overlap_safe_or_through
#print axioms crossing_unsafe_overlap_cross_exponent_credit

end DirectionData
end JSP000404Research
