import JSP000404Research.FullQuotientZeroAngleMass
import Mathlib.Tactic

/-!
# Averaging three zero-quotient angle positions

A five-ray centre has five cyclic quotient positions.  If positive support is
two, exactly three positions have quotient zero.

This file packages the elementary averaging step needed in the six-point
support-two branch: if the total actual-angle mass on the three zero positions
is at most B, then at least one zero position carries angle at most B/3.
-/

namespace JSP000404Research

def zeroAngleEntries : List ℕ → List ℝ → List ℝ
  | [], [] => []
  | q :: qs, A :: As =>
      (if q = 0 then [A] else []) ++ zeroAngleEntries qs As
  | _, _ => []

theorem zeroAngleEntries_sum
    (qs : List ℕ) (As : List ℝ)
    (hlen : qs.length = As.length) :
    (zeroAngleEntries qs As).sum =
      listZeroAngleMass qs As := by
  induction qs generalizing As with
  | nil =>
      cases As <;> simp [zeroAngleEntries, listZeroAngleMass]
  | cons q qs ih =>
      cases As with
      | nil => simp at hlen
      | cons A As =>
          simp only [List.length_cons, Nat.succ.injEq] at hlen
          by_cases hq : q = 0
          · subst q
            simp [zeroAngleEntries, listZeroAngleMass, ih As hlen]
          · simp [zeroAngleEntries, listZeroAngleMass, hq, ih As hlen]

theorem zeroAngleEntries_length
    (qs : List ℕ) (As : List ℝ)
    (hlen : qs.length = As.length) :
    (zeroAngleEntries qs As).length =
      qs.length - listPositiveCount qs := by
  induction qs generalizing As with
  | nil =>
      cases As <;> simp [zeroAngleEntries, listPositiveCount]
  | cons q qs ih =>
      cases As with
      | nil => simp at hlen
      | cons A As =>
          simp only [List.length_cons, Nat.succ.injEq] at hlen
          by_cases hq : q = 0
          · subst q
            simp [zeroAngleEntries, listPositiveCount, ih As hlen]
          · have hpos : 0 < listPositiveCount (q :: qs) := by
              simp [listPositiveCount, hq]
            simp [zeroAngleEntries, listPositiveCount, hq, ih As hlen]
            omega

theorem mem_zeroAngleEntries
    {qs : List ℕ} {As : List ℝ} {A : ℝ}
    (h : A ∈ zeroAngleEntries qs As) :
    ∃ preQ postQ : List ℕ,
      ∃ preA postA : List ℝ,
        qs = preQ ++ 0 :: postQ ∧
        As = preA ++ A :: postA ∧
        preQ.length = preA.length := by
  induction qs generalizing As with
  | nil =>
      cases As <;> simp [zeroAngleEntries] at h
  | cons q qs ih =>
      cases As with
      | nil => simp [zeroAngleEntries] at h
      | cons B Bs =>
          by_cases hq : q = 0
          · subst q
            simp only [zeroAngleEntries, if_pos, List.singleton_append,
                List.mem_cons] at h
            rcases h with rfl | htail
            · exact ⟨[], qs, [], Bs, rfl, rfl, rfl⟩
            · obtain ⟨preQ,postQ,preA,postA,hQ,hA,hLen⟩ :=
                ih (As := Bs) htail
              exact ⟨0 :: preQ, postQ, B :: preA, postA,
                by simp [hQ], by simp [hA], by simp [hLen]⟩
          · simp only [zeroAngleEntries, if_neg hq,
                List.nil_append] at h
            obtain ⟨preQ,postQ,preA,postA,hQ,hA,hLen⟩ :=
              ih (As := Bs) h
            exact ⟨q :: preQ, postQ, B :: preA, postA,
              by simp [hQ], by simp [hA], by simp [hLen]⟩

theorem exists_le_third_of_length_three_sum_le
    (xs : List ℝ)
    (h0 : ∀ x ∈ xs, 0 ≤ x)
    (hlen : xs.length = 3)
    {B : ℝ}
    (hsum : xs.sum ≤ B) :
    ∃ x ∈ xs, x ≤ B / 3 := by
  obtain ⟨a,b,c,rfl⟩ := List.length_eq_three.mp hlen
  by_contra hnone
  push_neg at hnone
  have ha := hnone a (by simp)
  have hb := hnone b (by simp)
  have hc := hnone c (by simp)
  simp at hsum
  nlinarith

/-- Five positions and support two give a small zero-quotient angle entry. -/
theorem exists_small_zeroAngleEntry_of_five_support_two
    (qs : List ℕ) (As : List ℝ)
    (hlenQ : qs.length = 5)
    (hlen : qs.length = As.length)
    (hsupport : listPositiveCount qs = 2)
    (hA0 : ∀ A ∈ As, 0 ≤ A)
    {B : ℝ}
    (hmass : listZeroAngleMass qs As ≤ B) :
    ∃ A ∈ zeroAngleEntries qs As,
      A ≤ B / 3 := by
  let zs := zeroAngleEntries qs As
  have hzlen : zs.length = 3 := by
    dsimp [zs]
    rw [zeroAngleEntries_length qs As hlen, hlenQ, hsupport]
    norm_num
  have hzsum : zs.sum ≤ B := by
    dsimp [zs]
    rw [zeroAngleEntries_sum qs As hlen]
    exact hmass
  have hz0 : ∀ A ∈ zs, 0 ≤ A := by
    intro A hA
    obtain ⟨preQ,postQ,preA,postA,hQ,hAs,hpre⟩ :=
      mem_zeroAngleEntries hA
    subst As
    exact hA0 A (by simp)
  exact exists_le_third_of_length_three_sum_le zs hz0 hzlen hzsum

#print axioms zeroAngleEntries_sum
#print axioms zeroAngleEntries_length
#print axioms exists_small_zeroAngleEntry_of_five_support_two

end JSP000404Research
