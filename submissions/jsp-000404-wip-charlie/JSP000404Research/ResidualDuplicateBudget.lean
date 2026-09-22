import JSP000404Research.ResidualActiveDrop
import JSP000404Research.ResidualHoleInjection
import JSP000404Research.ResidualSameCodeOrientation
import JSP000404Research.ResidualLightFibreDyadic
import JSP000404Research.ResidualBlockerDensity
import Mathlib.Tactic

/-!
# Exact retained budgets on duplicated retained-code fibres

The residual route does not have a global exact retained-palette bound.  The
available geometric estimate is only the one-layer bound

  card(active(v)) <= n - exponent(v) + 1.

However duplicated retained-code fibres are special.

If u<v have the same retained Boolean code, their joining edge must be the
residual colour.  Hence the residual colour is active at both u and v.
ResidualActiveDrop then removes the extra +1 at both endpoints:

  card(retainedActive(u)) <= n - exponent(u),
  card(retainedActive(v)) <= n - exponent(v).

Therefore every genuinely hard duplicate fibre automatically lies in the
exact-budget regime needed by the heavy/light residual repair lemmas, even
though arbitrary vertices need not.

This is the bridge between one-layer phase loss and the residual fibre
machinery.
-/

namespace JSP000404Research
namespace OrderedEdgeColoring

/-- A same-retained ordered pair uses the residual colour, hence residual is
active at both endpoints. -/
theorem residual_mem_active_both_of_sameRetained_lt
    {V : Type*} [LinearOrder V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    {u v : V}
    (huv : u < v)
    (hsame : SameRetained C u v) :
    residualCoord n ∈ active C u ∧
      residualCoord n ∈ active C v := by
  have hres := isResidual_of_sameRetained_lt C huv hsame
  exact residualCoord_mem_active_of_isResidual C huv hres

/-- The one-layer active bound upgrades to an exact retained bound at the
lower endpoint of every duplicated retained-code fibre. -/
theorem retainedActive_le_complement_left_of_sameRetained
    {V : Type*} [LinearOrder V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (honeLoss :
      ∀ x, (active C x).card ≤ n - exponent x + 1)
    {u v : V}
    (huv : u < v)
    (hsame : SameRetained C u v) :
    (retainedActive C u).card ≤ n - exponent u := by
  exact retainedActive_card_le_of_active_le_add_one_of_residual_mem
    C u (honeLoss u)
    (residual_mem_active_both_of_sameRetained_lt C huv hsame).1

/-- Same exact retained budget at the upper endpoint. -/
theorem retainedActive_le_complement_right_of_sameRetained
    {V : Type*} [LinearOrder V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (honeLoss :
      ∀ x, (active C x).card ≤ n - exponent x + 1)
    {u v : V}
    (huv : u < v)
    (hsame : SameRetained C u v) :
    (retainedActive C v).card ≤ n - exponent v := by
  exact retainedActive_card_le_of_active_le_add_one_of_residual_mem
    C v (honeLoss v)
    (residual_mem_active_both_of_sameRetained_lt C huv hsame).2

/-- Pairwise exact-budget package for a duplicated retained-code fibre. -/
theorem sameRetained_exact_pair_budget
    {V : Type*} [LinearOrder V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (honeLoss :
      ∀ x, (active C x).card ≤ n - exponent x + 1)
    {u v : V}
    (huv : u < v)
    (hsame : SameRetained C u v) :
    (retainedActive C u).card ≤ n - exponent u ∧
      (retainedActive C v).card ≤ n - exponent v := by
  exact ⟨
    retainedActive_le_complement_left_of_sameRetained
      C exponent honeLoss huv hsame,
    retainedActive_le_complement_right_of_sameRetained
      C exponent honeLoss huv hsame⟩

/-- Heavy duplicate fibres admit a common-inactive Boolean hole using only
the global one-layer active bound.  Exact retained budgets are recovered
locally from the residual edge, so no global retained-budget hypothesis is
needed. -/
theorem duplicate_heavy_has_common_inactive_hole
    {V : Type*} [LinearOrder V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexp : ∀ x, exponent x ≤ n)
    (honeLoss :
      ∀ x, (active C x).card ≤ n - exponent x + 1)
    {u v : V}
    (huv : u < v)
    (hsame : SameRetained C u v)
    (hheavy : n < exponent u + exponent v) :
    ∃ c : Fin n,
      c ∉ retainedActive C u ∧
      c ∉ retainedActive C v ∧
      ¬ ∃ w : V,
        (fun d => retainedBit C w d) =
          flippedRetainedCode C u c := by
  have hpair :=
    sameRetained_exact_pair_budget
      C exponent honeLoss huv hsame
  have hdef :
      (n - exponent u) + (n - exponent v) < n := by
    have hu := hexp u
    have hv := hexp v
    omega
  obtain ⟨c, hcu, hcv⟩ :=
    exists_common_inactive_of_deficit_sum_lt
      C hpair.1 hpair.2 hdef
  refine ⟨c, hcu, hcv, ?_⟩
  exact no_vertex_retainedCode_eq_flipped_common_inactive
    C c (ne_of_lt huv) hsame hcu hcv

/-- Heavy duplicate fibres therefore have a globally unoccupied one-coordinate
repair code whose coordinate is inactive at both endpoints. -/
theorem duplicate_heavy_has_free_flip
    {V : Type*} [LinearOrder V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexp : ∀ x, exponent x ≤ n)
    (honeLoss :
      ∀ x, (active C x).card ≤ n - exponent x + 1)
    {u v : V}
    (huv : u < v)
    (hsame : SameRetained C u v)
    (hheavy : n < exponent u + exponent v) :
    ∃ c : Fin n,
      c ∈ retainedInactive C u ∧
      c ∉ retainedActive C v ∧
      ¬ ∃ w : V,
        (fun d => retainedBit C w d) =
          flippedRetainedCode C u c := by
  obtain ⟨c, hcu, hcv, hfree⟩ :=
    duplicate_heavy_has_common_inactive_hole
      C exponent hexp honeLoss huv hsame hheavy
  exact ⟨c, (mem_retainedInactive C u c).2 hcu, hcv, hfree⟩

/-- Under the one-layer global bound, a duplicate fibre with no common
inactive coordinate satisfies the strengthened lightness estimate directly. -/
theorem duplicate_exponent_sum_add_commonIncoming_le
    {V : Type*} [LinearOrder V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (honeLoss :
      ∀ x, (active C x).card ≤ n - exponent x + 1)
    {u v : V}
    (huv : u < v)
    (hsame : SameRetained C u v)
    (hno :
      ¬ ∃ c : Fin n,
        c ∉ retainedActive C u ∧
        c ∉ retainedActive C v) :
    exponent u + exponent v +
        (incomingRetained C u).card ≤ n := by
  have hpair :=
    sameRetained_exact_pair_budget
      C exponent honeLoss huv hsame
  have hcard :=
    retained_card_sum_ge_n_add_commonIncoming
      C hsame hno
  omega

/-- Direct positive-light-fibre dyadic bound from the one-layer phase budget. -/
theorem duplicate_positive_light_fibre_dyadic_capacity
    {V : Type*} [LinearOrder V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (honeLoss :
      ∀ x, (active C x).card ≤ n - exponent x + 1)
    {u v : V}
    (huv : u < v)
    (hsame : SameRetained C u v)
    (hno :
      ¬ ∃ c : Fin n,
        c ∉ retainedActive C u ∧
        c ∉ retainedActive C v)
    (huPos : 1 ≤ exponent u)
    (hvPos : 1 ≤ exponent v) :
    2 ^ exponent u + 2 ^ exponent v ≤
      2 ^ (n - (incomingRetained C u).card) := by
  have hlight :=
    duplicate_exponent_sum_add_commonIncoming_le
      C exponent honeLoss huv hsame hno
  have hsum :
      exponent u + exponent v ≤
        n - (incomingRetained C u).card := by
    omega
  exact two_pow_add_le_two_pow_of_pos_sum_le
    huPos hvPos hsum

/-- If all inactive one-coordinate flips at the lower endpoint are occupied,
the lower exponent is bounded by the number of vertices to the right of the
upper endpoint.  The exact budget needed here is automatic on duplicate
fibres. -/
theorem duplicate_left_exponent_le_right_count_of_all_flips_occupied
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexp : ∀ x, exponent x ≤ n)
    (honeLoss :
      ∀ x, (active C x).card ≤ n - exponent x + 1)
    {u v : V}
    (huv : u < v)
    (hsame : SameRetained C u v)
    (hoccupied :
      ∀ c, c ∈ retainedInactive C u →
        ∃ w : V,
          (fun d => retainedBit C w d) =
            flippedRetainedCode C u c) :
    exponent u ≤ (strictRightVertices v).card := by
  have hretu :=
    retainedActive_le_complement_left_of_sameRetained
      C exponent honeLoss huv hsame
  have hkInactive :=
    exponent_le_retainedInactive_card_of_local_bound
      C (hexp u) hretu
  have hblocked :
      ∀ c, c ∈ retainedInactive C u →
        ∃ w : V, RetainedNeighbourBlocker C u c w := by
    intro c hc
    obtain ⟨w, hw⟩ := hoccupied c hc
    exact ⟨w,
      (retainedCode_eq_flipped_iff_blocker C u w c).1 hw⟩
  exact hkInactive.trans
    (retainedInactive_card_le_right_of_blocked
      C huv hsame hblocked)

/-- Rank-sensitive Boolean hole: if fewer than exponent(u) vertices remain to
the right of the upper endpoint, some inactive one-coordinate neighbour of the
lower endpoint is globally unoccupied. -/
theorem duplicate_has_free_flip_of_right_count_lt_exponent
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexp : ∀ x, exponent x ≤ n)
    (honeLoss :
      ∀ x, (active C x).card ≤ n - exponent x + 1)
    {u v : V}
    (huv : u < v)
    (hsame : SameRetained C u v)
    (hright :
      (strictRightVertices v).card < exponent u) :
    ∃ c : Fin n,
      c ∈ retainedInactive C u ∧
      ¬ ∃ w : V,
        (fun d => retainedBit C w d) =
          flippedRetainedCode C u c := by
  by_contra hno
  push_neg at hno
  have hoccupied :
      ∀ c, c ∈ retainedInactive C u →
        ∃ w : V,
          (fun d => retainedBit C w d) =
            flippedRetainedCode C u c := by
    intro c hc
    exact hno c hc
  have hle :=
    duplicate_left_exponent_le_right_count_of_all_flips_occupied
      C exponent hexp honeLoss huv hsame hoccupied
  omega

/-- Extremal right-edge case: if the upper endpoint is maximal and the lower
endpoint has positive exponent, a free one-coordinate retained-code neighbour
exists automatically. -/
theorem duplicate_has_free_flip_of_upper_maximal
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexp : ∀ x, exponent x ≤ n)
    (honeLoss :
      ∀ x, (active C x).card ≤ n - exponent x + 1)
    {u v : V}
    (huv : u < v)
    (hsame : SameRetained C u v)
    (hvmax : ∀ w : V, ¬ v < w)
    (hupos : 0 < exponent u) :
    ∃ c : Fin n,
      c ∈ retainedInactive C u ∧
      ¬ ∃ w : V,
        (fun d => retainedBit C w d) =
          flippedRetainedCode C u c := by
  have hrightZero :
      (strictRightVertices v).card = 0 := by
    classical
    unfold strictRightVertices
    rw [Finset.card_filter_eq_zero_iff]
    intro w _
    exact hvmax w
  apply duplicate_has_free_flip_of_right_count_lt_exponent
    C exponent hexp honeLoss huv hsame
  rw [hrightZero]
  exact hupos

#print axioms residual_mem_active_both_of_sameRetained_lt
#print axioms retainedActive_le_complement_left_of_sameRetained
#print axioms retainedActive_le_complement_right_of_sameRetained
#print axioms sameRetained_exact_pair_budget
#print axioms duplicate_heavy_has_common_inactive_hole
#print axioms duplicate_heavy_has_free_flip
#print axioms duplicate_exponent_sum_add_commonIncoming_le
#print axioms duplicate_positive_light_fibre_dyadic_capacity
#print axioms duplicate_left_exponent_le_right_count_of_all_flips_occupied
#print axioms duplicate_has_free_flip_of_right_count_lt_exponent
#print axioms duplicate_has_free_flip_of_upper_maximal

end OrderedEdgeColoring
end JSP000404Research
