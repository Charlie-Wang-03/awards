import JSP000404Research.PlanarThreeFiveNoTripleLossFibre
import JSP000404Research.ResidualLossGlobalNonlocalShortfallLedger
import Mathlib.Tactic

/-!
# Genuine n=3 five-centre global duplicate-debt quantitative improvement

The kernel-proved six-centre triple-fibre obstruction shows that with
<=5 original source vertices and exponents <=2, each ACTUAL opposite
corner q has at most TWO canonical earliest-prior collision records.
Summing the EXACT ORIGINAL source fibres, not pairwise surrogate sums,
improves Ddup <= 3 * |O| to Ddup <= 2 * |O|.

Consequently the exact original candidate REUSE deficit is at most
|O|, in the first n=3/5-centre open dyadic capacity regime.

Planar corollary instantiates the genuine AngleCap standard
residual colouring and actual centre cycles without additional
assumptions about available exterior true holes or payment.
-/

namespace JSP000404Research
namespace OrderedEdgeColoring

/-- Every genuine earliest-prior duplicate-debt record appears in
exactly ONE fibre indexed by its actual opposite Boolean candidate.
This is an unconditional finite map conservation identity. -/
theorem actual_loss_duplicate_debt_eq_sum_opposite_fibre_card
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ) (choice : V → Fin n) :
    translatedLossDuplicateDebt C exponent choice =
      ∑ q ∈ actualLossEarliestOppositeCandidateWords C exponent choice,
        (actualLossOppositeCandidateFibre C exponent choice q).card := by
  classical
  let S := actualEarliestLossCollisionRecords C exponent choice
  let f : (Fin n × Fin n × (Fin n → Bool)) → (Fin n → Bool) :=
    fun a => flipBoolWordAt (flipBoolWordAt a.2.2 a.1) a.2.1
  have hsum : S.card =
      ∑ q ∈ S.image f, (S.filter (fun a => f a = q)).card := by
    exact Finset.card_eq_sum_card_fiberwise
      (fun s hs => Finset.mem_image.mpr ⟨s, hs, rfl⟩)
  calc
    translatedLossDuplicateDebt C exponent choice = S.card :=
      (actual_earliest_collision_records_card_eq_duplicate_debt
        C exponent choice).symm
    _ = ∑ q ∈ S.image f, (S.filter (fun a => f a = q)).card := hsum
    _ = ∑ q ∈ actualLossEarliestOppositeCandidateWords
          C exponent choice,
          (actualLossOppositeCandidateFibre C exponent choice q).card := rfl

/-- Five original centres force the ACTUAL global canonical
duplicate debt to use at most TWO real records per distinct
Boolean opposite candidate q. No true-hole credit is asserted. -/
theorem actual_three_colour_five_centre_duplicate_debt_le_twice_candidates
    {V : Type*} [LinearOrder V] [Fintype V]
    (C : OrderedEdgeColoring V (3 + 1))
    (exponent : V → ℕ) (choice : V → Fin 3)
    (hexp : ∀ v, exponent v ≤ 2)
    (hfive : Fintype.card V ≤ 5) :
    translatedLossDuplicateDebt C exponent choice ≤
      2 * (actualLossEarliestOppositeCandidateWords
        C exponent choice).card := by
  classical
  let O := actualLossEarliestOppositeCandidateWords C exponent choice
  have hsum :=
    actual_loss_duplicate_debt_eq_sum_opposite_fibre_card
      C exponent choice
  have hbound :
      (∑ q ∈ O,
        (actualLossOppositeCandidateFibre C exponent choice q).card) ≤
      ∑ q ∈ O, (2 : ℕ) := by
    apply Finset.sum_le_sum
    intro q hq
    exact actual_three_colour_five_centre_no_triple_loss_fibre
      C exponent choice hexp hfive q
  have hconst : (∑ q ∈ O, (2 : ℕ)) = 2 * O.card := by
    simp [mul_comm]
  dsimp only [O] at hbound hconst
  omega

/-- The exact true-candidate REUSE deficit, which appears on the
LEFT of the previous global nonlocal-payment equivalence, is
bounded by the number of DISTINCT original opposite words for
n=3, <=5 centres and genuine centre exponent<=2. -/
theorem actual_three_colour_five_centre_reuse_defect_le_candidate_card
    {V : Type*} [LinearOrder V] [Fintype V]
    (C : OrderedEdgeColoring V (3 + 1))
    (exponent : V → ℕ) (choice : V → Fin 3)
    (hexp : ∀ v, exponent v ≤ 2)
    (hfive : Fintype.card V ≤ 5) :
    translatedLossDuplicateDebt C exponent choice -
        (actualLossEarliestOppositeCandidateWords
          C exponent choice).card ≤
      (actualLossEarliestOppositeCandidateWords
        C exponent choice).card := by
  have h := actual_three_colour_five_centre_duplicate_debt_le_twice_candidates
    C exponent choice hexp hfive
  omega

#print axioms actual_loss_duplicate_debt_eq_sum_opposite_fibre_card
#print axioms actual_three_colour_five_centre_duplicate_debt_le_twice_candidates
#print axioms actual_three_colour_five_centre_reuse_defect_le_candidate_card

end OrderedEdgeColoring

namespace ProjectionOrdered

open OrderedEdgeColoring
open DirectionData

/-- The above TWO-per-candidate original collision bound holds for
actual n=3 five-centre planar AngleCap configurations under the genuine
standard residual edge colouring and cycle-derived exponents. -/
theorem planar_three_five_standard_duplicate_debt_le_twice_candidates
    {V : Type*} [Fintype V]
    {p : V → Plane}
    (hp : Function.Injective p)
    {lam t delta : ℝ}
    (hcap : AngleCap p lam)
    (hfive : Fintype.card V ≤ 5)
    (hdelta0 : 0 ≤ delta)
    (hdeltaHalf : delta < (1 : ℝ) / 2)
    (ht : t = (3 : ℝ) + delta)
    (hlam : lam = Real.pi / t)
    (cycles :
      letI : LinearOrder (ProjectionOrdered V) :=
        projectionLinearOrder hp
      ∀ i : ProjectionOrdered V,
        CentreProjectiveCycle (reindexedPoint_injective hp) i) :
    letI : LinearOrder (ProjectionOrdered V) :=
      projectionLinearOrder hp
    let htpos : 0 < t := by rw [ht]; linarith
    let hwidth : t < (3 : ℝ) + 1 := by rw [ht]; linarith
    let D := genericDirectionData_sendov hp hcap htpos hlam
    let B := standardResidualColoring D 3 (by exact_mod_cast hwidth)
    let k : ProjectionOrdered V → ℕ :=
      fun i => centreExponent (cycles i) t
    ∀ (choice : ProjectionOrdered V → Fin 3),
      translatedLossDuplicateDebt B k choice ≤
        2 * (actualLossEarliestOppositeCandidateWords B k choice).card := by
  classical
  letI : LinearOrder (ProjectionOrdered V) := projectionLinearOrder hp
  have htpos : 0 < t := by rw [ht]; linarith
  have hwidth : t < (3 : ℝ) + 1 := by rw [ht]; linarith
  let D := genericDirectionData_sendov hp hcap htpos hlam
  let B : OrderedEdgeColoring (ProjectionOrdered V) (3 + 1) :=
    standardResidualColoring D 3 (by exact_mod_cast hwidth)
  let k : ProjectionOrdered V → ℕ :=
    fun i => centreExponent (cycles i) t
  change ∀ (choice : ProjectionOrdered V → Fin 3),
      translatedLossDuplicateDebt B k choice ≤
        2 * (actualLossEarliestOppositeCandidateWords B k choice).card
  have hdelta1 : delta < 1 := by linarith
  have hk : ∀ i : ProjectionOrdered V, k i ≤ 2 := by
    intro i
    have hi := centreExponent_lt_n
      (cycles i) 3 delta t (by decide : 1 ≤ (3 : ℕ))
      hdelta0 hdelta1 ht
    dsimp only [k]
    omega
  have hsize : Fintype.card (ProjectionOrdered V) ≤ 5 := by
    have heq : Fintype.card (ProjectionOrdered V) = Fintype.card V := by
      let e : ProjectionOrdered V ≃ V :=
        { toFun := ProjectionOrdered.toOriginal
          invFun := ProjectionOrdered.ofOriginal
          left_inv := fun _ => rfl
          right_inv := fun _ => rfl }
      exact Fintype.card_congr e
    omega
  intro choice
  exact actual_three_colour_five_centre_duplicate_debt_le_twice_candidates
    B k choice hk hsize

#print axioms planar_three_five_standard_duplicate_debt_le_twice_candidates

end ProjectionOrdered
end JSP000404Research
