import JSP000404Research.ResidualCompletionMultiplicity
import JSP000404Research.ResidualEnlargedCandidateBlock
import JSP000404Research.MinimalBlockDeficiency
import Mathlib.Tactic

/-!
# Unconditional weighted subset expansion for strictly non-loss centres

Retained completion cubes have wordwise multiplicity at most two, proved
by the ordered-residual-edge geometry of the Boolean encoding.

If every v in a chosen finite subset S has a strict projected slack layer
  exponent(v) < projectedFree(C,v),
then 2 * 2^exponent(v) <= |Q_v|.  Summing and using bounded cube
multiplicity gives
  2 * sum_v 2^exponent(v) <= sum_v |Q_v|
                             <= 2 * |union_v Q_v|.
Cancellation yields Hall expansion for that entire subset, with no
assumption on centres outside S.

In particular every deficient enlarged-block set must include a vertex
at which exponent(v) >= projectedFree(v): either an exact non-loss
centre or a projected-loss centre in the one-layer regime.

This is an unconditional reduction of geometry gap G1, NOT its
complete proof: exact non-loss cores can still require compensation.
-/

namespace JSP000404Research
namespace OrderedEdgeColoring

/-- Retained completion mass for any vertex subset is no more than twice
the cardinality of its union, by the established pointwise
two-carrier rigidity. -/
theorem subset_completion_cube_mass_le_two_mul_union
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (S : Finset V) :
    (∑ v ∈ S, (retainedCompletionWords C v).card) ≤
      2 * (S.biUnion (retainedCompletionWords C)).card := by
  classical
  let B : V → Finset (Fin n → Bool) := retainedCompletionWords C
  let U : Finset (Fin n → Bool) := S.biUnion B
  have hfibre :
      ∀ word : Fin n → Bool,
        (S.filter (fun v => word ∈ B v)).card ≤ 2 := by
    intro word
    have hsub :
        S.filter (fun v => word ∈ B v) ⊆
          completionFibre C word := by
      intro v hv
      exact (mem_completionFibre C word v).2
        (Finset.mem_filter.mp hv).2
    exact (Finset.card_le_card hsub).trans
      (completionFibre_card_le_two C word)
  have hmass :
      (∑ v ∈ S, (B v).card) =
        ∑ word ∈ U, (S.filter (fun v => word ∈ B v)).card := by
    calc
      (∑ v ∈ S, (B v).card) =
        ∑ v ∈ S,
          ∑ word ∈ U, if word ∈ B v then 1 else 0 := by
            apply Finset.sum_congr rfl
            intro v hv
            have hsub : B v ⊆ U := by
              intro word hw
              exact Finset.mem_biUnion.mpr ⟨v, hv, hw⟩
            exact Finset.card_eq_sum_ite hsub
      _ =
        ∑ word ∈ U,
          ∑ v ∈ S, if word ∈ B v then 1 else 0 := by
            rw [Finset.sum_comm]
      _ =
        ∑ word ∈ U, (S.filter (fun v => word ∈ B v)).card := by
            apply Finset.sum_congr rfl
            intro word hw
            symm
            exact Finset.card_filter _ _
  have htwo :
      (∑ word ∈ U, (S.filter (fun v => word ∈ B v)).card) ≤
        ∑ word ∈ U, 2 := by
    apply Finset.sum_le_sum
    intro word hw
    exact hfibre word
  have hsum : (∑ word ∈ U, (2 : ℕ)) = 2 * U.card := by
    simp [mul_comm]
  change (∑ v ∈ S, (B v).card) ≤ 2 * U.card
  exact hmass.le.trans (htwo.trans_eq hsum)

/-- Any finite subset of exclusively strict-projected-slack vertices
has no enlarged-block weighted Hall deficiency, regardless of any
other vertices in the full planar configuration. -/
theorem strict_nonloss_subset_enlarged_hall_expansion
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (S : Finset V)
    (hstrict : ∀ v ∈ S, exponent v < projectedFree C v) :
    (∑ v ∈ S, 2 ^ exponent v) ≤
      (S.biUnion (enlargedProjectedCandidateBlock C exponent)).card := by
  classical
  have hnonloss :
      ∀ v ∈ S, v ∉ projectedLossVertices C exponent := by
    intro v hv hvLoss
    have heq := (mem_projectedLossVertices C exponent v).1 hvLoss
    have hlt := hstrict v hv
    omega
  have hunion :
      S.biUnion (enlargedProjectedCandidateBlock C exponent) =
        S.biUnion (retainedCompletionWords C) := by
    apply Finset.biUnion_congr rfl
    intro v hv
    exact enlargedProjectedCandidateBlock_nonloss
      C exponent (hnonloss v hv)
  have hperVertex :
      ∀ v ∈ S, 2 * 2 ^ exponent v ≤
        (retainedCompletionWords C v).card := by
    intro v hv
    rw [retainedCompletionWords_card]
    change 2 * 2 ^ exponent v ≤ 2 ^ projectedFree C v
    have hle :
        exponent v + 1 ≤ projectedFree C v := by
      have hlt := hstrict v hv
      omega
    have hpow :
        2 ^ (exponent v + 1) ≤ 2 ^ (projectedFree C v) :=
      Nat.pow_le_pow_right (by norm_num : 0 < 2) hle
    simpa [pow_succ, mul_comm] using hpow
  have hsum :
      2 * (∑ v ∈ S, 2 ^ exponent v) ≤
        ∑ v ∈ S, (retainedCompletionWords C v).card := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro v hv
    exact hperVertex v hv
  have hdouble :
      (∑ v ∈ S, (retainedCompletionWords C v).card) ≤
        2 * (S.biUnion (retainedCompletionWords C)).card :=
    subset_completion_cube_mass_le_two_mul_union C S
  rw [hunion]
  omega

/-- Every deficient enlarged-block set contains a non-strict
centre. This narrows the open loss-existence gap G1 to the exact
non-loss boundary, instead of arbitrary strict non-loss vertices. -/
theorem deficient_enlarged_core_has_exact_or_loss_profile
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    {T : Finset V}
    (hdef :
      BlockDeficient
        (fun i => 2 ^ exponent i)
        (enlargedProjectedCandidateBlock C exponent) T) :
    ∃ v ∈ T, projectedFree C v ≤ exponent v := by
  classical
  by_contra hno
  push Not at hno
  have hstrict :
      ∀ v ∈ T, exponent v < projectedFree C v := by
    intro v hv
    exact hno v hv
  have hexpand :=
    strict_nonloss_subset_enlarged_hall_expansion
      C exponent T hstrict
  change
    (T.biUnion (enlargedProjectedCandidateBlock C exponent)).card <
      (∑ v ∈ T, 2 ^ exponent v) at hdef
  exact (Nat.not_lt_of_ge hexpand) hdef

#print axioms subset_completion_cube_mass_le_two_mul_union
#print axioms strict_nonloss_subset_enlarged_hall_expansion
#print axioms deficient_enlarged_core_has_exact_or_loss_profile

end OrderedEdgeColoring
end JSP000404Research
