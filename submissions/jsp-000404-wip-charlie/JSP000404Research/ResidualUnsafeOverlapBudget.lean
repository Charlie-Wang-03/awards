
import JSP000404Research.ResidualUnsafeOverlap
import JSP000404Research.ResidualSliceSeparation
import Mathlib.Tactic

/-!
# Only both-saturated unsafe overlaps have a genuine unit defect

For a residual-active vertex v let

  nu(v) = projectedFree(v) = n-card(retainedActive(v)).

The one-layer active bound upgrades to exponent(v) <= nu(v).

If an unsafe residual pair u<v carries a projected overlap word, its retained
completion-cube intersection is a singleton.  Hence

  card(Q_u union Q_v) = 2^nu(u) + 2^nu(v) - 1.

If exponent is strictly smaller than nu at at least one endpoint, the missing
one word is paid by that endpoint's dyadic slack.  Therefore

  2^k(u)+2^k(v) <= card(Q_u union Q_v).

The only remaining internal obstruction is exact saturation at both endpoints:

  k(u)=nu(u),  k(v)=nu(v),

in which case the target pair mass exceeds its own completion union by exactly
one Boolean word.

This isolates the true global residual defect to both-saturated unsafe overlap
edges.
-/

namespace JSP000404Research
namespace OrderedEdgeColoring

def ProjectedSaturated
    {V : Type*} [LinearOrder V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (v : V) : Prop :=
  exponent v = projectedFree C v

/-- Exact union cardinality for an unsafe overlapping pair. -/
theorem unsafe_overlap_union_card_add_one
    {V : Type*} [LinearOrder V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    {u v : V}
    (hunsafe :
      ¬ ∃ c : Fin n, c ∉ residualForbidden C u v)
    {base : Fin n → Bool}
    (hbaseU : base ∈ retainedCompletionWords C u)
    (hbaseV : base ∈ retainedCompletionWords C v) :
    (retainedCompletionWords C u ∪
      retainedCompletionWords C v).card + 1 =
      2 ^ projectedFree C u +
        2 ^ projectedFree C v := by
  have hinter :=
    retainedCompletionWords_inter_card_eq_one_of_unsafe_overlap
      C hunsafe hbaseU hbaseV
  have hcard :=
    Finset.card_union_add_card_inter
      (retainedCompletionWords C u)
      (retainedCompletionWords C v)
  rw [hinter,
      retainedCompletionWords_card,
      retainedCompletionWords_card] at hcard
  rfl at hcard ⊢
  omega

/-- A residual endpoint is exactly budgeted after projection. -/
theorem exponent_le_projectedFree_of_residual_endpoint
    {V : Type*} [LinearOrder V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexp : ∀ x, exponent x ≤ n)
    (honeLoss :
      ∀ x, (active C x).card ≤ n - exponent x + 1)
    {u v : V}
    (huv : u < v)
    (hres : IsResidual C u v) :
    exponent u ≤ projectedFree C u ∧
      exponent v ≤ projectedFree C v := by
  have hactive :=
    residualCoord_mem_active_of_isResidual C huv hres
  constructor
  · exact exponent_le_projectedFree_of_residual_mem
      C exponent hexp honeLoss hactive.1
  · exact exponent_le_projectedFree_of_residual_mem
      C exponent hexp honeLoss hactive.2

/-- If at least one endpoint has strict projected slack, the pair's target
mass fits in its own completion union despite the singleton overlap. -/
theorem unsafe_overlap_pair_mass_le_union_of_one_strict
    {V : Type*} [LinearOrder V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    {u v : V}
    (hu : exponent u ≤ projectedFree C u)
    (hv : exponent v ≤ projectedFree C v)
    (hstrict :
      exponent u < projectedFree C u ∨
      exponent v < projectedFree C v)
    (hunsafe :
      ¬ ∃ c : Fin n, c ∉ residualForbidden C u v)
    {base : Fin n → Bool}
    (hbaseU : base ∈ retainedCompletionWords C u)
    (hbaseV : base ∈ retainedCompletionWords C v) :
    2 ^ exponent u + 2 ^ exponent v ≤
      (retainedCompletionWords C u ∪
        retainedCompletionWords C v).card := by
  have hU :
      2 ^ exponent u ≤ 2 ^ projectedFree C u :=
    Nat.pow_le_pow_right (by norm_num : 0 < 2) hu
  have hV :
      2 ^ exponent v ≤ 2 ^ projectedFree C v :=
    Nat.pow_le_pow_right (by norm_num : 0 < 2) hv
  have hone :
      2 ^ exponent u + 2 ^ exponent v + 1 ≤
        2 ^ projectedFree C u +
          2 ^ projectedFree C v := by
    rcases hstrict with hUstrict | hVstrict
    · have hU1 :=
        pow_two_add_one_le_of_lt hUstrict
      omega
    · have hV1 :=
        pow_two_add_one_le_of_lt hVstrict
      omega
  have hunion :=
    unsafe_overlap_union_card_add_one
      C hunsafe hbaseU hbaseV
  omega

/-- If both endpoints saturate projected free count, the pair has exact
one-code internal deficit. -/
theorem unsafe_overlap_pair_mass_eq_union_add_one_of_both_saturated
    {V : Type*} [LinearOrder V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    {u v : V}
    (hu : ProjectedSaturated C exponent u)
    (hv : ProjectedSaturated C exponent v)
    (hunsafe :
      ¬ ∃ c : Fin n, c ∉ residualForbidden C u v)
    {base : Fin n → Bool}
    (hbaseU : base ∈ retainedCompletionWords C u)
    (hbaseV : base ∈ retainedCompletionWords C v) :
    2 ^ exponent u + 2 ^ exponent v =
      (retainedCompletionWords C u ∪
        retainedCompletionWords C v).card + 1 := by
  unfold ProjectedSaturated at hu hv
  rw [hu, hv]
  symm
  exact unsafe_overlap_union_card_add_one
    C hunsafe hbaseU hbaseV

/-- Complete pair-level dichotomy under the actual residual one-layer
hypotheses. -/
theorem unsafe_overlap_internal_dichotomy
    {V : Type*} [LinearOrder V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexp : ∀ x, exponent x ≤ n)
    (honeLoss :
      ∀ x, (active C x).card ≤ n - exponent x + 1)
    {u v : V}
    (huv : u < v)
    (hres : IsResidual C u v)
    (hunsafe :
      ¬ ∃ c : Fin n, c ∉ residualForbidden C u v)
    {base : Fin n → Bool}
    (hbaseU : base ∈ retainedCompletionWords C u)
    (hbaseV : base ∈ retainedCompletionWords C v) :
    (2 ^ exponent u + 2 ^ exponent v ≤
      (retainedCompletionWords C u ∪
        retainedCompletionWords C v).card)
    ∨
    (ProjectedSaturated C exponent u ∧
      ProjectedSaturated C exponent v ∧
      2 ^ exponent u + 2 ^ exponent v =
        (retainedCompletionWords C u ∪
          retainedCompletionWords C v).card + 1) := by
  have hbudget :=
    exponent_le_projectedFree_of_residual_endpoint
      C exponent hexp honeLoss huv hres
  by_cases huSat :
      exponent u = projectedFree C u
  · by_cases hvSat :
        exponent v = projectedFree C v
    · right
      exact ⟨huSat, hvSat,
        unsafe_overlap_pair_mass_eq_union_add_one_of_both_saturated
          C exponent huSat hvSat hunsafe hbaseU hbaseV⟩
    · left
      apply unsafe_overlap_pair_mass_le_union_of_one_strict
        C exponent hbudget.1 hbudget.2
      · right
        omega
      · exact hunsafe
      · exact hbaseU
      · exact hbaseV
  · left
    apply unsafe_overlap_pair_mass_le_union_of_one_strict
      C exponent hbudget.1 hbudget.2
    · left
      omega
    · exact hunsafe
    · exact hbaseU
    · exact hbaseV

#print axioms unsafe_overlap_union_card_add_one
#print axioms unsafe_overlap_pair_mass_le_union_of_one_strict
#print axioms unsafe_overlap_pair_mass_eq_union_add_one_of_both_saturated
#print axioms unsafe_overlap_internal_dichotomy

end OrderedEdgeColoring
end JSP000404Research
