import JSP000404Research.ListZeroGapMass
import Mathlib.Tactic

/-!
# Pointwise gap remainder bound under full quotient mass

For aligned quotient/gap lists with

  gaps.sum = 1,
  quotients.sum = n,
  t = n + delta,

the total fractional remainder is exactly delta.  Every individual remainder

  t*g - q

is nonnegative, hence at most delta.  Therefore every displayed aligned entry
satisfies

  t*g <= q + delta.

The q=1 specialization is the critical unit-gap upper bound
t*g <= 1+delta.
-/

namespace JSP000404Research

/-- Aligned quotient/gap lists have nonnegative total remainder mass. -/
theorem listRemainderMass_nonneg_of_aligned
    {t : ℝ} {qs : List ℕ} {gs : List ℝ}
    (halign : QuotientGapAligned t qs gs) :
    0 ≤ listRemainderMass t qs gs := by
  induction halign with
  | nil =>
      simp [listRemainderMass]
  | @cons q g qs gs hqg htail ih =>
      simp only [listRemainderMass]
      have hhead : 0 ≤ t * g - (q : ℝ) := by
        linarith
      linarith

/-- A displayed aligned entry contributes at most the total remainder mass. -/
theorem displayed_remainder_le_listRemainderMass
    {t : ℝ}
    (qpre qpost : List ℕ)
    (gpre gpost : List ℝ)
    (q : ℕ) (ge : ℝ)
    (hpreLen : qpre.length = gpre.length)
    (halign :
      QuotientGapAligned t
        (qpre ++ q :: qpost)
        (gpre ++ ge :: gpost)) :
    t * ge - (q : ℝ) ≤
      listRemainderMass t
        (qpre ++ q :: qpost)
        (gpre ++ ge :: gpost) := by
  induction qpre generalizing gpre with
  | nil =>
      have hgpre : gpre = [] :=
        List.length_eq_zero.mp (by simpa using hpreLen.symm)
      subst gpre
      simp only [List.nil_append] at halign ⊢
      cases halign with
      | cons hqge htail =>
          simp only [listRemainderMass]
          have htail0 :=
            listRemainderMass_nonneg_of_aligned htail
          linarith
  | cons q0 qpre ih =>
      cases gpre with
      | nil =>
          simp at hpreLen
      | cons g0 gpre =>
          simp only [List.length_cons, Nat.succ.injEq] at hpreLen
          simp only [List.cons_append] at halign ⊢
          cases halign with
          | cons hq0 htail =>
              simp only [listRemainderMass]
              have hhead0 : 0 ≤ t * g0 - (q0 : ℝ) := by
                linarith
              have hih :=
                ih gpre hpreLen htail
              linarith

/-- Full-mass pointwise remainder bound. -/
theorem displayed_gap_scaled_le_quotient_add_delta
    {t delta : ℝ} {n : ℕ}
    (qpre qpost : List ℕ)
    (gpre gpost : List ℝ)
    (q : ℕ) (ge : ℝ)
    (ht : t = (n : ℝ) + delta)
    (hpreLen : qpre.length = gpre.length)
    (hgapsum :
      (gpre ++ ge :: gpost).sum = 1)
    (hqsum :
      (qpre ++ q :: qpost).sum = n)
    (halign :
      QuotientGapAligned t
        (qpre ++ q :: qpost)
        (gpre ++ ge :: gpost)) :
    t * ge ≤ (q : ℝ) + delta := by
  have hlen :
      (qpre ++ q :: qpost).length =
        (gpre ++ ge :: gpost).length :=
    quotientGapAligned_length halign
  have hrem :=
    displayed_remainder_le_listRemainderMass
      qpre qpost gpre gpost q ge
      hpreLen halign
  have htotal :=
    listRemainderMass_eq t
      (qpre ++ q :: qpost)
      (gpre ++ ge :: gpost)
      hlen
  rw [ht, hgapsum, hqsum] at htotal
  norm_num at htotal
  rw [htotal] at hrem
  linarith

/-- Unit-gap specialization. -/
theorem displayed_unit_gap_scaled_le_one_add_delta
    {t delta : ℝ} {n : ℕ}
    (qpre qpost : List ℕ)
    (gpre gpost : List ℝ)
    (ge : ℝ)
    (ht : t = (n : ℝ) + delta)
    (hpreLen : qpre.length = gpre.length)
    (hgapsum :
      (gpre ++ ge :: gpost).sum = 1)
    (hqsum :
      (qpre ++ 1 :: qpost).sum = n)
    (halign :
      QuotientGapAligned t
        (qpre ++ 1 :: qpost)
        (gpre ++ ge :: gpost)) :
    t * ge ≤ 1 + delta := by
  simpa using
    displayed_gap_scaled_le_quotient_add_delta
      qpre qpost gpre gpost 1 ge
      ht hpreLen hgapsum hqsum halign

#print axioms listRemainderMass_nonneg_of_aligned
#print axioms displayed_remainder_le_listRemainderMass
#print axioms displayed_gap_scaled_le_quotient_add_delta
#print axioms displayed_unit_gap_scaled_le_one_add_delta

end JSP000404Research
