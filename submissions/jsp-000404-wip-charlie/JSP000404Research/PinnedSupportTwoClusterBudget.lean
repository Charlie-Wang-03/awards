import JSP000404Research.SupportTwoPinnedCycle
import JSP000404Research.ListZeroGapMass
import Mathlib.Tactic

/-!
# Quantitative middle-cluster budget in the pinned support-two cycle

After pinning a distinguished ray at the cut, the desired support-two shape is

  quotients = qFirst :: mid ++ [qLast]

with qFirst,qLast positive and every entry of mid zero.

For aligned geometric gaps

  gaps = gFirst :: gmid ++ [gLast],

the list zero-gap mass is therefore exactly gmid.sum.  Since the quotient sum
is n and the normalized gaps sum to one, the global remainder identity gives

  t * gmid.sum <= delta.

The number of middle gaps is arbitrary.  This is the quantitative replacement
for the unique-zero-gap estimate used in the Fin 4 terminal.
-/

namespace JSP000404Research

theorem listZeroGapMass_pinned_support_two_eq_middle_sum
    (qFirst qLast : ℕ)
    (mid : List ℕ)
    (gFirst gLast : ℝ)
    (gmid : List ℝ)
    (hFirst : qFirst ≠ 0)
    (hLast : qLast ≠ 0)
    (hlen : mid.length = gmid.length)
    (hzero : ∀ q ∈ mid, q = 0) :
    listZeroGapMass
        (qFirst :: (mid ++ [qLast]))
        (gFirst :: (gmid ++ [gLast]))
      =
    gmid.sum := by
  simp only [listZeroGapMass, hFirst, if_false, zero_add]
  have hmid :
      listZeroGapMass mid gmid = gmid.sum :=
    listZeroGapMass_eq_gap_sum_of_all_zero
      mid gmid hlen hzero
  induction mid generalizing gmid with
  | nil =>
      have hgmid : gmid = [] :=
        List.length_eq_zero.mp (by simpa using hlen.symm)
      subst gmid
      simp [listZeroGapMass, hLast]
  | cons q qs ih =>
      cases gmid with
      | nil =>
          simp at hlen
      | cons g gs =>
          simp at hlen
          have hq0 : q = 0 := hzero q (by simp)
          have htail : ∀ x ∈ qs, x = 0 := by
            intro x hx
            exact hzero x (by simp [hx])
          subst q
          simp [listZeroGapMass, hLast,
            ih gs hlen htail]

theorem pinned_support_two_middle_scaled_le_delta
    (qFirst qLast : ℕ)
    (mid : List ℕ)
    (gFirst gLast : ℝ)
    (gmid : List ℝ)
    {n : ℕ} {delta t : ℝ}
    (hFirst : 1 ≤ qFirst)
    (hLast : 1 ≤ qLast)
    (hsupport :
      listPositiveCount
        (qFirst :: mid ++ [qLast]) = 2)
    (hlen : mid.length = gmid.length)
    (ht : t = (n : ℝ) + delta)
    (hqsum :
      (qFirst :: mid ++ [qLast]).sum = n)
    (hgapsum :
      (gFirst :: gmid ++ [gLast]).sum = 1)
    (halign :
      QuotientGapAligned t
        (qFirst :: mid ++ [qLast])
        (gFirst :: gmid ++ [gLast])) :
    t * gmid.sum ≤ delta := by
  have hzero :
      ∀ q ∈ mid, q = 0 := by
    have hz :=
      support_two_end_positive_forces_zero_middle
        qFirst qLast mid hFirst hLast hsupport
    exact (positiveCount_eq_zero_iff_all_zero mid).1 hz
  have hmass :=
    listZeroGapMass_scaled_le_delta
      (qFirst :: mid ++ [qLast])
      (gFirst :: gmid ++ [gLast])
      ht hgapsum hqsum halign
  have hmassEq :=
    listZeroGapMass_pinned_support_two_eq_middle_sum
      qFirst qLast mid gFirst gLast gmid
      (by omega) (by omega) hlen hzero
  rw [hmassEq] at hmass
  exact hmass

/-- Same conclusion when end positivity is obtained abstractly by excluding
zero at the two pinned ends. -/
theorem pinned_support_two_middle_scaled_le_delta_of_end_zero_impossible
    (qFirst qLast : ℕ)
    (mid : List ℕ)
    (gFirst gLast : ℝ)
    (gmid : List ℝ)
    {n : ℕ} {delta t : ℝ}
    (hFirstZero : qFirst = 0 → False)
    (hLastZero : qLast = 0 → False)
    (hsupport :
      listPositiveCount
        (qFirst :: mid ++ [qLast]) = 2)
    (hlen : mid.length = gmid.length)
    (ht : t = (n : ℝ) + delta)
    (hqsum :
      (qFirst :: mid ++ [qLast]).sum = n)
    (hgapsum :
      (gFirst :: gmid ++ [gLast]).sum = 1)
    (halign :
      QuotientGapAligned t
        (qFirst :: mid ++ [qLast])
        (gFirst :: gmid ++ [gLast])) :
    t * gmid.sum ≤ delta := by
  have hshape :=
    pinned_support_two_shape_of_end_zero_impossible
      qFirst qLast mid
      hFirstZero hLastZero hsupport
  exact pinned_support_two_middle_scaled_le_delta
    qFirst qLast mid gFirst gLast gmid
    hshape.1 hshape.2.1 hsupport hlen
    ht hqsum hgapsum halign

#print axioms listZeroGapMass_pinned_support_two_eq_middle_sum
#print axioms pinned_support_two_middle_scaled_le_delta
#print axioms pinned_support_two_middle_scaled_le_delta_of_end_zero_impossible

end JSP000404Research
