
import JSP000404Research.ResidualUnsafeSaturatedBlock
import Mathlib.Data.Finset.SDiff
import Mathlib.Tactic

/-!
# Boolean orientation blocks for saturated unsafe overlaps

For an unsafe projected-overlap carrier u<v, the orientation nesting gives

  incoming(v) subset incoming(u),
  outgoing(u) subset outgoing(v),

and the crossed inner sets

  incoming(v), outgoing(u)

are disjoint.

Define the orientation block B(u,v) by fixing

* every colour in incoming(v) to true;
* every colour in outgoing(u) to false.

Both retained completion cubes Q_u and Q_v lie inside B(u,v).

For a both-saturated carrier, the number of free coordinates of B is exactly

  exponent(u) + exponent(v),

so

  card B = 2^(exponent(u)+exponent(v)).

If both endpoint exponents are positive, the elementary dyadic inequality

  2^ku + 2^kv <= 2^(ku+kv)

shows that B has enough capacity for the target pair.  Since the actual pair
completion union has cardinality exactly one less than its target mass, there
is always at least one word of B outside Q_u union Q_v.

This pair-local hole is the natural starting point for a Boolean displacement
chain.  It need not yet be a global hole: a third completion cube may occupy
it, in which case that vertex becomes the next blocker.
-/

namespace JSP000404Research

/-- Generic partial Boolean completion predicate. -/
def FixedCompletes
    {n : ℕ}
    (bit : Fin n → Bool)
    (specified : Finset (Fin n))
    (word : Fin n → Bool) : Prop :=
  ∀ c, c ∈ specified → word c = bit c

noncomputable def fixedCompletionWords
    {n : ℕ}
    (bit : Fin n → Bool)
    (specified : Finset (Fin n)) :
    Finset (Fin n → Bool) := by
  classical
  exact Finset.univ.filter (FixedCompletes bit specified)

@[simp] theorem mem_fixedCompletionWords
    {n : ℕ}
    (bit : Fin n → Bool)
    (specified : Finset (Fin n))
    (word : Fin n → Bool) :
    word ∈ fixedCompletionWords bit specified ↔
      FixedCompletes bit specified word := by
  classical
  simp [fixedCompletionWords]

noncomputable def fixedCompletionEquivFree
    {n : ℕ}
    (bit : Fin n → Bool)
    (specified : Finset (Fin n)) :
    FreeCoordinates specified ≃
      {word : Fin n → Bool //
        word ∈ fixedCompletionWords bit specified} where
  toFun free := ⟨
    fun c =>
      if hc : c ∈ specified then bit c else free ⟨c, hc⟩,
    by
      apply (mem_fixedCompletionWords bit specified _).2
      intro c hc
      simp [hc]⟩
  invFun word :=
    fun c => word.1 c.1
  left_inv free := by
    funext c
    simp [c.2]
  right_inv word := by
    apply Subtype.ext
    funext c
    by_cases hc : c ∈ specified
    · have hcomp :=
        (mem_fixedCompletionWords bit specified word.1).1 word.2
      simp [hc, hcomp c hc]
    · simp [hc]

theorem fixedCompletionWords_card
    {n : ℕ}
    (bit : Fin n → Bool)
    (specified : Finset (Fin n)) :
    (fixedCompletionWords bit specified).card =
      2 ^ (n - specified.card) := by
  classical
  have hcard :=
    Fintype.card_congr
      (fixedCompletionEquivFree bit specified)
  rw [card_freeCoordinates] at hcard
  simpa using hcard.symm

namespace OrderedEdgeColoring

noncomputable def orientationSpecified
    {V : Type*} [LinearOrder V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (u v : V) : Finset (Fin n) :=
  incomingRetained C v ∪ outgoingRetained C u

noncomputable def orientationBit
    {V : Type*} [LinearOrder V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (v : V) : Fin n → Bool :=
  fun c => decide (c ∈ incomingRetained C v)

noncomputable def orientationBlock
    {V : Type*} [LinearOrder V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (u v : V) : Finset (Fin n → Bool) :=
  fixedCompletionWords
    (orientationBit C v)
    (orientationSpecified C u v)

@[simp] theorem mem_orientationBlock
    {V : Type*} [LinearOrder V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (u v : V) (word : Fin n → Bool) :
    word ∈ orientationBlock C u v ↔
      FixedCompletes
        (orientationBit C v)
        (orientationSpecified C u v)
        word := by
  simp [orientationBlock]

/-- Under overlap, the two inner orientation sets are disjoint. -/
theorem orientation_inner_disjoint_of_overlap
    {V : Type*} [LinearOrder V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    {u v : V} {word : Fin n → Bool}
    (huWord : word ∈ retainedCompletionWords C u)
    (hvWord : word ∈ retainedCompletionWords C v) :
    Disjoint
      (incomingRetained C v)
      (outgoingRetained C u) := by
  exact
    (outgoing_inter_incoming_eq_empty_of_completion_overlap
      C huWord hvWord |>
      Finset.disjoint_iff_inter_eq_empty.mpr).symm

/-- The lower endpoint completion cube lies in its unsafe-overlap orientation
block. -/
theorem retainedCompletionWords_subset_orientationBlock_left
    {V : Type*} [LinearOrder V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    {u v : V} {base : Fin n → Bool}
    (hunsafe :
      ¬ ∃ c : Fin n, c ∉ residualForbidden C u v)
    (huBase : base ∈ retainedCompletionWords C u)
    (hvBase : base ∈ retainedCompletionWords C v) :
    retainedCompletionWords C u ⊆
      orientationBlock C u v := by
  intro word huWord
  apply (mem_orientationBlock C u v word).2
  intro c hc
  rw [orientationSpecified, Finset.mem_union] at hc
  rcases hc with hcInV | hcOutU
  · have hsub :=
      incomingRetained_subset_incomingRetained_of_unsafe_overlap
        C hunsafe huBase hvBase
    have hcInU := hsub hcInV
    have hcActiveU :=
      incomingRetained_subset_retainedActive C u hcInU
    have hcomp :=
      (mem_retainedCompletionWords C u word).1 huWord
    have hbit :
        retainedBit C u c = true :=
      (mem_incomingRetained_iff_retainedBit_true
        C u c).1 hcInU
    have hw : word c = true :=
      (hcomp c hcActiveU).trans hbit
    simp [orientationBit, hcInV, hw]
  · have hcActiveU :=
      outgoingRetained_subset_retainedActive C u hcOutU
    have hcomp :=
      (mem_retainedCompletionWords C u word).1 huWord
    have hfalse :
        retainedBit C u c = false := by
      have hnotIn :
          c ∉ incomingRetained C u := by
        intro hcin
        exact Finset.disjoint_left.mp
          (incomingRetained_disjoint_outgoingRetained C u)
          hcin hcOutU
      exact
        (mem_incomingRetained_iff_retainedBit_true
          C u c).not.mp hnotIn |>
        (by
          intro hne
          cases h : retainedBit C u c <;> simp_all)
    have hcNotInV :
        c ∉ incomingRetained C v := by
      intro hInV
      have hcross :=
        outgoing_inter_incoming_eq_empty_of_completion_overlap
          C huBase hvBase
      have hcInter :
          c ∈ outgoingRetained C u ∩ incomingRetained C v :=
        Finset.mem_inter.mpr ⟨hcOutU, hInV⟩
      rw [hcross] at hcInter
      simp at hcInter
    have hw := hcomp c hcActiveU
    rw [hfalse] at hw
    simp [orientationBit, hcNotInV, hw]

/-- The upper endpoint completion cube also lies in the same orientation
block. -/
theorem retainedCompletionWords_subset_orientationBlock_right
    {V : Type*} [LinearOrder V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    {u v : V} {base : Fin n → Bool}
    (hunsafe :
      ¬ ∃ c : Fin n, c ∉ residualForbidden C u v)
    (huBase : base ∈ retainedCompletionWords C u)
    (hvBase : base ∈ retainedCompletionWords C v) :
    retainedCompletionWords C v ⊆
      orientationBlock C u v := by
  intro word hvWord
  apply (mem_orientationBlock C u v word).2
  intro c hc
  rw [orientationSpecified, Finset.mem_union] at hc
  rcases hc with hcInV | hcOutU
  · have hcActiveV :=
      incomingRetained_subset_retainedActive C v hcInV
    have hcomp :=
      (mem_retainedCompletionWords C v word).1 hvWord
    have hbit :
        retainedBit C v c = true :=
      (mem_incomingRetained_iff_retainedBit_true
        C v c).1 hcInV
    have hw : word c = true :=
      (hcomp c hcActiveV).trans hbit
    simp [orientationBit, hcInV, hw]
  · have hsub :=
      outgoingRetained_subset_outgoingRetained_of_unsafe_overlap
        C hunsafe huBase hvBase
    have hcOutV := hsub hcOutU
    have hcActiveV :=
      outgoingRetained_subset_retainedActive C v hcOutV
    have hcomp :=
      (mem_retainedCompletionWords C v word).1 hvWord
    have hfalse :=
      retainedBit_false_of_outgoingRetained C hcOutV
    have hcNotInV :
        c ∉ incomingRetained C v := by
      intro hInV
      exact Finset.disjoint_left.mp
        (incomingRetained_disjoint_outgoingRetained C v)
        hInV hcOutV
    have hw := hcomp c hcActiveV
    rw [hfalse] at hw
    simp [orientationBit, hcNotInV, hw]

theorem retainedCompletionWords_union_subset_orientationBlock
    {V : Type*} [LinearOrder V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    {u v : V} {base : Fin n → Bool}
    (hunsafe :
      ¬ ∃ c : Fin n, c ∉ residualForbidden C u v)
    (huBase : base ∈ retainedCompletionWords C u)
    (hvBase : base ∈ retainedCompletionWords C v) :
    retainedCompletionWords C u ∪
        retainedCompletionWords C v
      ⊆ orientationBlock C u v := by
  exact Finset.union_subset
    (retainedCompletionWords_subset_orientationBlock_left
      C hunsafe huBase hvBase)
    (retainedCompletionWords_subset_orientationBlock_right
      C hunsafe huBase hvBase)

/-- Cardinality of the orientation block under overlap. -/
theorem orientationBlock_card_of_overlap
    {V : Type*} [LinearOrder V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    {u v : V} {base : Fin n → Bool}
    (huBase : base ∈ retainedCompletionWords C u)
    (hvBase : base ∈ retainedCompletionWords C v) :
    (orientationBlock C u v).card =
      2 ^ (n -
        ((incomingRetained C v).card +
         (outgoingRetained C u).card)) := by
  rw [orientationBlock, fixedCompletionWords_card]
  have hdisj :
      Disjoint
        (incomingRetained C v)
        (outgoingRetained C u) :=
    orientation_inner_disjoint_of_overlap
      C huBase hvBase
  have hcard :
      (orientationSpecified C u v).card =
        (incomingRetained C v).card +
          (outgoingRetained C u).card := by
    unfold orientationSpecified
    exact Finset.card_union_of_disjoint hdisj
  rw [hcard]

/-- For a both-saturated unsafe overlap, the orientation block dimension is
exactly the sum of the two endpoint exponents. -/
theorem orientationBlock_card_of_unsafe_saturated_overlap
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    {u v : V} {base : Fin n → Bool}
    (huBase : base ∈ retainedCompletionWords C u)
    (hvBase : base ∈ retainedCompletionWords C v)
    (hunsafe :
      ¬ ∃ c : Fin n, c ∉ residualForbidden C u v)
    (huSat : ExactProjectedBudget C exponent u)
    (hvSat : ExactProjectedBudget C exponent v) :
    (orientationBlock C u v).card =
      2 ^ (exponent u + exponent v) := by
  rw [orientationBlock_card_of_overlap
      C huBase hvBase]
  have hdim :=
    unsafe_saturated_overlap_exponent_sum_eq_remaining_dimension
      C exponent huBase hvBase hunsafe huSat hvSat
  rw [← hdim]

/-- Positive both-saturated carriers have at least one pair-local Boolean hole
inside their orientation block. -/
theorem exists_orientationBlock_word_outside_pair
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    {u v : V} {base : Fin n → Bool}
    (huBase : base ∈ retainedCompletionWords C u)
    (hvBase : base ∈ retainedCompletionWords C v)
    (hunsafe :
      ¬ ∃ c : Fin n, c ∉ residualForbidden C u v)
    (huSat : ExactProjectedBudget C exponent u)
    (hvSat : ExactProjectedBudget C exponent v)
    (huPos : 1 ≤ exponent u)
    (hvPos : 1 ≤ exponent v) :
    ∃ word : Fin n → Bool,
      word ∈ orientationBlock C u v ∧
      word ∉
        (retainedCompletionWords C u ∪
          retainedCompletionWords C v) := by
  classical
  have hsub :=
    retainedCompletionWords_union_subset_orientationBlock
      C hunsafe huBase hvBase
  have hpair :=
    unsafe_overlap_pair_mass_eq_union_add_one_of_both_saturated
      C exponent huSat hvSat hunsafe huBase hvBase
  have hblock :=
    orientationBlock_card_of_unsafe_saturated_overlap
      C exponent huBase hvBase hunsafe huSat hvSat
  have hmass :
      2 ^ exponent u + 2 ^ exponent v ≤
        2 ^ (exponent u + exponent v) :=
    two_pow_add_le_two_pow_of_pos_sum_le
      huPos hvPos le_rfl
  have hlt :
      (retainedCompletionWords C u ∪
        retainedCompletionWords C v).card <
      (orientationBlock C u v).card := by
    rw [hblock]
    omega
  exact Finset.exists_mem_notMem_of_card_lt_card hlt

#print axioms fixedCompletionWords_card
#print axioms retainedCompletionWords_union_subset_orientationBlock
#print axioms orientationBlock_card_of_unsafe_saturated_overlap
#print axioms exists_orientationBlock_word_outside_pair

end OrderedEdgeColoring
end JSP000404Research
