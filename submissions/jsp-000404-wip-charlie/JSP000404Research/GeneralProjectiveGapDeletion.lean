import JSP000404Research.CyclicProjectiveGaps
import JSP000404Research.FloorMergeCarry
import JSP000404Research.CentreQuotientData
import Mathlib.Tactic

/-!
# Arbitrary-length deletion of the first projective ray

For a nonempty sorted projective angle list

  a :: b :: bs,

the parent normalized cyclic gaps have the form

  gFirst :: middle ++ [gLast],

where

  gFirst = (b-a)/pi,
  middle = successive gaps from b through bs,
  gLast = (a+pi-last)/pi.

After deleting the first ray a, the child gaps are exactly

  middle ++ [gLast + gFirst].

Thus at fixed nonnegative Sendov scale t, every quotient is unchanged except
for the cyclicly merged final quotient

  qLast + qFirst + carry,

with binary carry <= 1.

This is the arbitrary-cardinality list-level deletion identity missing from
the earlier three-ray deletion module.
-/

namespace JSP000404Research

open Real

def normalizedSuccessiveTail (b : ℝ) (bs : List ℝ) : List ℝ :=
  (successiveDiffsFrom b bs).map (fun g => g / Real.pi)

def firstNormalizedGap (a b : ℝ) : ℝ :=
  (b - a) / Real.pi

def lastNormalizedGap (a b : ℝ) (bs : List ℝ) : ℝ :=
  (a + Real.pi - bs.getLastD b) / Real.pi

theorem normalizedProjectiveGaps_cons_cons_parent
    (a b : ℝ) (bs : List ℝ) :
    normalizedProjectiveGaps (a :: b :: bs) =
      firstNormalizedGap a b ::
        (normalizedSuccessiveTail b bs ++
          [lastNormalizedGap a b bs]) := by
  simp [normalizedProjectiveGaps, projectiveGaps,
    successiveDiffsFrom, normalizedSuccessiveTail,
    firstNormalizedGap, lastNormalizedGap,
    List.getLastD_cons, List.map_append]

theorem normalizedProjectiveGaps_delete_first_general
    (a b : ℝ) (bs : List ℝ) :
    normalizedProjectiveGaps (b :: bs) =
      normalizedSuccessiveTail b bs ++
        [lastNormalizedGap a b bs +
          firstNormalizedGap a b] := by
  simp [normalizedProjectiveGaps, projectiveGaps,
    normalizedSuccessiveTail, firstNormalizedGap,
    lastNormalizedGap, List.map_append]
  congr 1
  field_simp [Real.pi_ne_zero]
  ring

theorem firstNormalizedGap_nonneg
    {a b : ℝ} (hab : a ≤ b) :
    0 ≤ firstNormalizedGap a b :=
  div_nonneg (sub_nonneg.mpr hab) Real.pi_pos.le

theorem lastNormalizedGap_nonneg
    {a b : ℝ} {bs : List ℝ}
    (ha0 : 0 ≤ a)
    (hlastPi : bs.getLastD b < Real.pi) :
    0 ≤ lastNormalizedGap a b bs := by
  unfold lastNormalizedGap
  apply div_nonneg
  · linarith
  · exact Real.pi_pos.le

/-- Parent quotient decomposition corresponding to the explicit parent gap
decomposition. -/
theorem quotientList_cons_cons_parent
    (t a b : ℝ) (bs : List ℝ) :
    quotientList t (normalizedProjectiveGaps (a :: b :: bs)) =
      Nat.floor (t * firstNormalizedGap a b) ::
        (quotientList t (normalizedSuccessiveTail b bs) ++
          [Nat.floor (t * lastNormalizedGap a b bs)]) := by
  rw [normalizedProjectiveGaps_cons_cons_parent]
  simp [quotientList, List.map_append]

/-- Child quotient list after deleting the first ray: only the two cyclic end
quotients merge, with one binary floor carry. -/
theorem quotientList_delete_first_general
    {t a b : ℝ} {bs : List ℝ}
    (ht : 0 ≤ t)
    (hab : a ≤ b)
    (ha0 : 0 ≤ a)
    (hlastPi : bs.getLastD b < Real.pi) :
    ∃ carry : ℕ,
      carry ≤ 1 ∧
      quotientList t (normalizedProjectiveGaps (b :: bs)) =
        quotientList t (normalizedSuccessiveTail b bs) ++
          [Nat.floor (t * lastNormalizedGap a b bs) +
            Nat.floor (t * firstNormalizedGap a b) + carry] := by
  have hfirst0 :
      0 ≤ firstNormalizedGap a b :=
    firstNormalizedGap_nonneg hab
  have hlast0 :
      0 ≤ lastNormalizedGap a b bs :=
    lastNormalizedGap_nonneg ha0 hlastPi
  obtain ⟨carry, hcarry, hmerge⟩ :=
    natFloor_scaled_gap_merge ht hlast0 hfirst0
  refine ⟨carry, hcarry, ?_⟩
  rw [normalizedProjectiveGaps_delete_first_general]
  simp only [quotientList, List.map_append,
    List.map_singleton]
  rw [hmerge]

/-- List-exponent consequence: if the parent first and final quotients are both
positive, deleting the first ray raises the quotient-list exponent by at least
one. -/
theorem listExponent_delete_first_general_gain
    {t a b : ℝ} {bs : List ℝ}
    (ht : 0 ≤ t)
    (hab : a ≤ b)
    (ha0 : 0 ≤ a)
    (hlastPi : bs.getLastD b < Real.pi)
    (hfirst :
      1 ≤ Nat.floor (t * firstNormalizedGap a b))
    (hlast :
      1 ≤ Nat.floor (t * lastNormalizedGap a b bs)) :
    listExponent
        (quotientList t
          (normalizedProjectiveGaps (a :: b :: bs))) + 1
      ≤
    listExponent
        (quotientList t
          (normalizedProjectiveGaps (b :: bs))) := by
  obtain ⟨carry, _, hchild⟩ :=
    quotientList_delete_first_general
      ht hab ha0 hlastPi
  rw [quotientList_cons_cons_parent, hchild]
  exact pinned_cyclic_merge_gain_of_end_positive
    (Nat.floor (t * firstNormalizedGap a b))
    (Nat.floor (t * lastNormalizedGap a b bs))
    carry
    (quotientList t (normalizedSuccessiveTail b bs))
    hfirst hlast

#print axioms normalizedProjectiveGaps_delete_first_general
#print axioms quotientList_delete_first_general
#print axioms listExponent_delete_first_general_gain

end JSP000404Research
