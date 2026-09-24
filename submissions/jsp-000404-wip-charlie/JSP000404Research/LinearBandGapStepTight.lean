
import JSP000404Research.LinearBandGapEquality
import Mathlib.Tactic

/-!
# Stepwise rigidity in an equality case of the interior band-gap bound

The interior inequality

  listExponent(successive floor gaps)
    + occupiedBandCount
      <= floor(last)-floor(first)+1

is proved by adding a nonnegative local slack at every adjacent sorted pair.

If the total interior inequality is an equality, every local slack must vanish.

For adjacent values a<=b there are two cases.

* Same occupied band:
    floor(a)=floor(b), hence floor(b-a)=0.

* New occupied band:
    floor(a)<floor(b), and equality forces
      excess(floor(b-a)) + 1 = floor(b)-floor(a).

The recursive predicate below records this exact stepwise tightness along the
entire sorted local direction list.
-/

namespace JSP000404Research

def InteriorBandGapTight : ℝ → List ℝ → Prop
  | _, [] => True
  | a, b :: bs =>
      (
        if Nat.floor a = Nat.floor b then
          Nat.floor (b - a) = 0
        else
          excess (Nat.floor (b - a)) + 1 =
            Nat.floor b - Nat.floor a
      )
      ∧
      InteriorBandGapTight b bs

@[simp] theorem interiorBandGapTight_nil
    (a : ℝ) :
    InteriorBandGapTight a [] := by
  simp [InteriorBandGapTight]

@[simp] theorem interiorBandGapTight_cons
    (a b : ℝ) (bs : List ℝ) :
    InteriorBandGapTight a (b :: bs) ↔
      (
        (if Nat.floor a = Nat.floor b then
            Nat.floor (b - a) = 0
          else
            excess (Nat.floor (b - a)) + 1 =
              Nat.floor b - Nat.floor a)
        ∧
        InteriorBandGapTight b bs
      ) := by
  rfl

/-- Equality in the total interior bound forces every adjacent step to be
tight. -/
theorem interior_gapEquality_implies_stepwise_tight
    (a : ℝ) (xs : List ℝ)
    (ha0 : 0 ≤ a)
    (hsorted : (a :: xs).Pairwise (· ≤ ·))
    (heq :
      listExponent
          ((successiveDiffsFrom a xs).map Nat.floor) +
          (occupiedNatBands (a :: xs)).card
        =
      Nat.floor (xs.getLastD a) - Nat.floor a + 1) :
    InteriorBandGapTight a xs := by
  induction xs generalizing a with
  | nil =>
      simp [InteriorBandGapTight]
  | cons b bs ih =>
      have hpair := List.pairwise_cons.mp hsorted
      have hab : a ≤ b :=
        hpair.1 b (by simp)
      have hb0 : 0 ≤ b := ha0.trans hab
      have htail :
          (b :: bs).Pairwise (· ≤ ·) :=
        hpair.2
      have htailLe :=
        interior_gapExponent_add_occupied_le_span
          b bs hb0 htail
      have hAB :
          Nat.floor a ≤ Nat.floor b :=
        Nat.floor_mono hab
      by_cases hEq :
          Nat.floor a = Nat.floor b
      · have hq0 :
            Nat.floor (b - a) = 0 :=
          natFloor_sub_eq_zero_of_floor_eq
            ha0 hab hEq
        have hbands :
            occupiedNatBands (a :: b :: bs) =
              occupiedNatBands (b :: bs) := by
          simp [occupiedNatBands, hEq]
        have htailEq :
            listExponent
                ((successiveDiffsFrom b bs).map Nat.floor) +
                (occupiedNatBands (b :: bs)).card
              =
            Nat.floor (bs.getLastD b) - Nat.floor b + 1 := by
          simp only [successiveDiffsFrom, List.map_cons,
            listExponent, List.map_cons, List.sum_cons] at heq
          rw [hq0, hbands, hEq] at heq
          simp [excess] at heq
          exact heq
        rw [InteriorBandGapTight]
        refine ⟨?_, ih b hb0 htail htailEq⟩
        simp [hEq, hq0]
      · have hLt :
            Nat.floor a < Nat.floor b := by
          omega
        have hnotmem :
            Nat.floor a ∉ occupiedNatBands (b :: bs) := by
          intro hmem
          rw [occupiedNatBands, List.mem_toFinset,
            List.mem_map] at hmem
          obtain ⟨x, hx, hxFloor⟩ := hmem
          have hBx :
              Nat.floor b ≤ Nat.floor x :=
            head_floor_le_of_mem_sorted
              htail hx
          rw [← hxFloor] at hBx
          omega
        have hbands :
            (occupiedNatBands (a :: b :: bs)).card =
              (occupiedNatBands (b :: bs)).card + 1 := by
          rw [occupiedNatBands_cons,
              Finset.card_insert_of_not_mem hnotmem]
          omega
        have hgapLe :
            excess (Nat.floor (b - a)) + 1 ≤
              Nat.floor b - Nat.floor a :=
          excess_natFloor_sub_add_one_le_floor_sub_of_floor_lt
            ha0 hab hLt
        have hBLast :
            Nat.floor b ≤
              Nat.floor (bs.getLastD b) :=
          floor_head_le_floor_getLastD_of_pairwise
            b bs htail
        have hgapEq :
            excess (Nat.floor (b - a)) + 1 =
              Nat.floor b - Nat.floor a := by
          simp only [successiveDiffsFrom, List.map_cons,
            listExponent, List.map_cons, List.sum_cons] at heq
          rw [hbands] at heq
          omega
        have htailEq :
            listExponent
                ((successiveDiffsFrom b bs).map Nat.floor) +
                (occupiedNatBands (b :: bs)).card
              =
            Nat.floor (bs.getLastD b) - Nat.floor b + 1 := by
          simp only [successiveDiffsFrom, List.map_cons,
            listExponent, List.map_cons, List.sum_cons] at heq
          rw [hbands] at heq
          omega
        rw [InteriorBandGapTight]
        refine ⟨?_, ih b hb0 htail htailEq⟩
        simp [hEq, hgapEq]

/-- Global cyclic equality implies stepwise interior tightness. -/
theorem linear_cyclic_gapEquality_implies_stepwise_tight
    {t : ℝ} {n : ℕ}
    (a : ℝ) (xs : List ℝ)
    (ha0 : 0 ≤ a)
    (hsorted : (a :: xs).Pairwise (· ≤ ·))
    (hall : ∀ x ∈ a :: xs, x < t)
    (ht : t < (n : ℝ) + 1)
    (heq :
      listExponent (linearCyclicGapQuotients t (a :: xs)) +
          (occupiedNatBands (a :: xs)).card
        =
      n + 1) :
    InteriorBandGapTight a xs := by
  have hinterior :=
    (linear_cyclic_gapEquality_splits
      a xs ha0 hsorted hall ht heq).1
  exact interior_gapEquality_implies_stepwise_tight
    a xs ha0 hsorted hinterior

/-- On any tight new-band step, a jump of at least two bands forces the gap
quotient itself to equal the whole band-index jump. -/
theorem floor_gap_eq_floor_jump_of_tight_of_two_le
    {a b : ℝ}
    (ha0 : 0 ≤ a)
    (hab : a ≤ b)
    (htight :
      excess (Nat.floor (b - a)) + 1 =
        Nat.floor b - Nat.floor a)
    (hjump :
      2 ≤ Nat.floor b - Nat.floor a) :
    Nat.floor (b - a) =
      Nat.floor b - Nat.floor a := by
  have hqLe :=
    natFloor_sub_le_floor_sub ha0 hab
  have hqPos :
      1 ≤ Nat.floor (b - a) := by
    unfold excess at htight
    omega
  unfold excess at htight
  omega

#print axioms interior_gapEquality_implies_stepwise_tight
#print axioms linear_cyclic_gapEquality_implies_stepwise_tight
#print axioms floor_gap_eq_floor_jump_of_tight_of_two_le

end JSP000404Research
