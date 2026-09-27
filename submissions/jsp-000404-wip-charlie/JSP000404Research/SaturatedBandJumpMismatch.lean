import JSP000404Research.CyclicBandGapDomination
import Mathlib.Tactic

/-!
# Zero-quotient / positive-band mismatches under exact exponent equality

Suppose two natural lists are position-aligned and satisfy q_i <= b_i.
Think of q_i as actual cyclic floor-gap quotients and b_i as cyclic jumps
between occupied unit-band labels.

Every positive q-position is automatically a positive b-position.  The only
extra positive b-positions are therefore positions with

  q_i = 0,   b_i > 0.

We count these explicitly.  If in addition the two lists have the same
listExponent, the pointwise excess inequalities must all be equalities.  At a
mismatch q_i=0<b_i this forces excess(b_i)=0, hence b_i=1.

This is the arithmetic atom behind the saturated four-band support shapes.
-/

namespace JSP000404Research

def zeroPositiveMismatchCount : List ℕ → List ℕ → ℕ
  | q :: qs, b :: bs =>
      (if q = 0 ∧ b ≠ 0 then 1 else 0) +
        zeroPositiveMismatchCount qs bs
  | _, _ => 0

theorem positiveCount_eq_add_mismatch_of_forall₂_le
    {qs bs : List ℕ}
    (h : List.Forall₂ (· ≤ ·) qs bs) :
    listPositiveCount bs =
      listPositiveCount qs +
        zeroPositiveMismatchCount qs bs := by
  induction h with
  | nil =>
      simp [listPositiveCount, zeroPositiveMismatchCount]
  | @cons q b qs bs hqb hrest ih =>
      by_cases hq0 : q = 0
      · subst q
        by_cases hb0 : b = 0
        · subst b
          simp [listPositiveCount,
            zeroPositiveMismatchCount, ih]
        · simp [listPositiveCount,
            zeroPositiveMismatchCount, hb0, ih]
      · have hb0 : b ≠ 0 := by
          intro hb
          subst b
          omega
        simp [listPositiveCount,
          zeroPositiveMismatchCount, hq0, hb0, ih]

theorem excess_mono_nat
    {q b : ℕ}
    (hqb : q ≤ b) :
    excess q ≤ excess b := by
  unfold excess
  omega

/-- Equality of total exponent under pointwise quotient domination forces
pointwise equality of every excess contribution. -/
theorem forall₂_excess_eq_of_forall₂_le_of_listExponent_eq
    {qs bs : List ℕ}
    (h : List.Forall₂ (· ≤ ·) qs bs)
    (hexp : listExponent qs = listExponent bs) :
    List.Forall₂
      (fun q b => excess q = excess b)
      qs bs := by
  induction h with
  | nil =>
      exact List.Forall₂.nil
  | @cons q b qs bs hqb hrest ih =>
      have hheadLe : excess q ≤ excess b :=
        excess_mono_nat hqb
      have htailLe :
          listExponent qs ≤ listExponent bs :=
        listExponent_le_of_forall₂_le hrest
      have hheadEq : excess q = excess b := by
        simp only [listExponent, List.map_cons,
          List.sum_cons] at hexp
        omega
      have htailEq :
          listExponent qs = listExponent bs := by
        simp only [listExponent, List.map_cons,
          List.sum_cons] at hexp
        omega
      exact List.Forall₂.cons hheadEq
        (ih htailEq)

/-- At an extra positive band-jump position, exact exponent equality forces
that jump to be exactly one unit. -/
theorem forall₂_mismatch_is_unit_of_exact_exponent
    {qs bs : List ℕ}
    (hle : List.Forall₂ (· ≤ ·) qs bs)
    (hexp : listExponent qs = listExponent bs) :
    List.Forall₂
      (fun q b =>
        q = 0 ∧ b ≠ 0 → b = 1)
      qs bs := by
  have heq :=
    forall₂_excess_eq_of_forall₂_le_of_listExponent_eq
      hle hexp
  induction heq with
  | nil =>
      exact List.Forall₂.nil
  | @cons q b qs bs hqb hrest ih =>
      apply List.Forall₂.cons
      · rintro ⟨hq0, hb0⟩
        subst q
        unfold excess at hqb
        have hbPos : 1 ≤ b := Nat.one_le_iff_ne_zero.mpr hb0
        omega
      · exact ih

/-- Numerical form: if the band-jump support has B positive positions and the
quotient support has Q, then the mismatch count is exactly B-Q. -/
theorem mismatchCount_eq_sub_positiveCounts
    {qs bs : List ℕ}
    (hle : List.Forall₂ (· ≤ ·) qs bs) :
    zeroPositiveMismatchCount qs bs =
      listPositiveCount bs - listPositiveCount qs := by
  have h :=
    positiveCount_eq_add_mismatch_of_forall₂_le hle
  omega

#print axioms positiveCount_eq_add_mismatch_of_forall₂_le
#print axioms forall₂_excess_eq_of_forall₂_le_of_listExponent_eq
#print axioms forall₂_mismatch_is_unit_of_exact_exponent
#print axioms mismatchCount_eq_sub_positiveCounts

end JSP000404Research
